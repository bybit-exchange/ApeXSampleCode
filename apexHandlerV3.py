import os
import base64
import hashlib
import hmac
import json
import requests
import urllib3
import time
import sys
import decimal
import math
from collections import namedtuple
from random import randint
DECIMAL_CONTEXT_ROUND_DOWN = decimal.Context(rounding=decimal.ROUND_DOWN)
DECIMAL_CONTEXT_ROUND_UP = decimal.Context(rounding=decimal.ROUND_UP)
DECIMAL_CTX_EXACT = decimal.Context(
    traps=[
        decimal.Inexact,
        decimal.DivisionByZero,
        decimal.InvalidOperation,
        decimal.Overflow,
    ],
)
def to_quantums_exact(human_amount,asset_resolution):
    return int((DECIMAL_CTX_EXACT.create_decimal(human_amount)*DECIMAL_CTX_EXACT.create_decimal(asset_resolution)).to_integral_exact(context=DECIMAL_CTX_EXACT))

def to_quantums_round_up(human_amount,asset_resolution):
    return int((DECIMAL_CONTEXT_ROUND_UP.create_decimal(human_amount)*DECIMAL_CONTEXT_ROUND_UP.create_decimal(asset_resolution)).to_integral_exact(context=DECIMAL_CONTEXT_ROUND_UP))

def to_quantums_round_down(human_amount,asset_resolution):
    return int((DECIMAL_CONTEXT_ROUND_DOWN.create_decimal(human_amount)*DECIMAL_CONTEXT_ROUND_DOWN.create_decimal(asset_resolution)).to_integral_exact(context=DECIMAL_CONTEXT_ROUND_DOWN))

COLLATERAL_ASSET = "USDC"
ASSET_RESOLUTION = {COLLATERAL_ASSET : '1e6'}
ORDER_FIELD_BIT_LENGTHS = {
    "asset_id_synthetic": 128,
    "asset_id_collateral": 250,
    "asset_id_fee": 250,
    "quantums_amount": 64,
    "nonce": 32,
    "position_id": 64,
    "expiration_epoch_hours": 32,
}
from ecdsa.rfc6979 import generate_k
from typing import Optional,Tuple
import sympy
from sympy.core.numbers import igcdex
ECPoint = Tuple[int, int]
ECSignature = Tuple[int, int]
PEDERSEN_HASH_POINT_FILENAME = os.path.join(
    os.path.dirname(__file__), 'pedersen_params.json')
PEDERSEN_PARAMS = json.load(open(PEDERSEN_HASH_POINT_FILENAME))

FIELD_PRIME = PEDERSEN_PARAMS['FIELD_PRIME']
FIELD_GEN = PEDERSEN_PARAMS['FIELD_GEN']
ALPHA = PEDERSEN_PARAMS['ALPHA']
BETA = PEDERSEN_PARAMS['BETA']
EC_ORDER = PEDERSEN_PARAMS['EC_ORDER']
CONSTANT_POINTS = PEDERSEN_PARAMS['CONSTANT_POINTS']

N_ELEMENT_BITS_ECDSA = math.floor(math.log(FIELD_PRIME, 2))
assert N_ELEMENT_BITS_ECDSA == 251

N_ELEMENT_BITS_HASH = FIELD_PRIME.bit_length()
assert N_ELEMENT_BITS_HASH == 252

# Elliptic curve parameters.
assert 2**N_ELEMENT_BITS_ECDSA < EC_ORDER < FIELD_PRIME

SHIFT_POINT = CONSTANT_POINTS[0]
MINUS_SHIFT_POINT = (SHIFT_POINT[0], FIELD_PRIME - SHIFT_POINT[1])
EC_GEN = CONSTANT_POINTS[1]

assert SHIFT_POINT == [0x49ee3eba8c1600700ee1b87eb599f16716b0b1022947733551fde4050ca6804,
                       0x3ca0cfe4b3bc6ddf346d49d06ea0ed34e621062c0e056c1d0405d266e10268a]
assert EC_GEN == [0x1ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca,
                  0x5668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f]

def ec_double(point: ECPoint, alpha: int, p: int) -> ECPoint:
    """
    Doubles a point on an elliptic curve with the equation y^2 = x^3 + alpha*x + beta mod p.
    Assumes the point is given in affine form (x, y) and has y != 0.
    """
    assert point[1] % p != 0
    m = div_mod(3 * point[0] * point[0] + alpha, 2 * point[1], p)
    x = (m * m - 2 * point[0]) % p
    y = (m * (point[0] - x) - point[1]) % p
    return x, y
def div_mod(n: int, m: int, p: int) -> int:
    """
    Finds a nonnegative integer 0 <= x < p such that (m * x) % p == n
    """
    a, b, c = igcdex(m, p)
    assert c == 1
    return (n * a) % p

def ec_add(point1: ECPoint, point2: ECPoint, p: int) -> ECPoint:
    """
    Gets two points on an elliptic curve mod p and returns their sum.
    Assumes the points are given in affine form (x, y) and have different x coordinates.
    """
    assert (point1[0] - point2[0]) % p != 0
    m = div_mod(point1[1] - point2[1], point1[0] - point2[0], p)
    x = (m * m - point1[0] - point2[0]) % p
    y = (m * (point1[0] - x) - point1[1]) % p
    return x, y

def ec_mult(m: int, point: ECPoint, alpha: int, p: int) -> ECPoint:
    """
    Multiplies by m a point on the elliptic curve with equation y^2 = x^3 + alpha*x + beta mod p.
    Assumes the point is given in affine form (x, y) and that 0 < m < order(point).
    """
    if m == 1:
        return point
    if m % 2 == 0:
        return ec_mult(m // 2, ec_double(point, alpha, p), alpha, p)
    return ec_add(ec_mult(m - 1, point, alpha, p), point, p)

def generate_k_rfc6979(msg_hash: int, priv_key: int, seed: Optional[int] = None) -> int:
    # Pad the message hash, for consistency with the elliptic.js library.
    if 1 <= msg_hash.bit_length() % 8 <= 4 and msg_hash.bit_length() >= 248:
        # Only if we are one-nibble short:
        msg_hash *= 16

    if seed is None:
        extra_entropy = b''
    else:
        extra_entropy = seed.to_bytes(math.ceil(seed.bit_length() / 8), 'big')

    return generate_k(EC_ORDER, priv_key, hashlib.sha256,
                      msg_hash.to_bytes(math.ceil(msg_hash.bit_length() / 8), 'big'),
                      extra_entropy=extra_entropy)
def py_sign(msg_hash: int, priv_key: int, seed: Optional[int] = None) -> ECSignature:
    assert 0 <= msg_hash < 2**N_ELEMENT_BITS_ECDSA, 'Message not signable.'
    while True:
        k = generate_k_rfc6979(msg_hash, priv_key, seed)
        if seed is None:
            seed = 1
        else:
            seed += 1

        x = ec_mult(k, EC_GEN, ALPHA, FIELD_PRIME)[0]

        r = int(x)
        if not (1 <= r < 2**N_ELEMENT_BITS_ECDSA):
            continue

        if (msg_hash + r * priv_key) % EC_ORDER == 0:
            continue

        w = div_mod(k, msg_hash + r * priv_key, EC_ORDER)
        if not (1 <= w < 2**N_ELEMENT_BITS_ECDSA):
            continue

        s = div_mod(1, w, EC_ORDER)
        return r, s

def serialize_signature(x,y):
    return hex(x)[2:].rjust(64, '0')+hex(y)[2:].rjust(64, '0')

def pedersen_hash_as_point(*elements: int) -> ECPoint:
    """
    Similar to pedersen_hash but also returns the y coordinate of the resulting EC point.
    This function is used for testing.
    """
    point = SHIFT_POINT
    for i, x in enumerate(elements):
        assert 0 <= x < FIELD_PRIME
        point_list = CONSTANT_POINTS[2 + i * N_ELEMENT_BITS_HASH:2 + (i + 1) * N_ELEMENT_BITS_HASH]
        assert len(point_list) == N_ELEMENT_BITS_HASH
        for pt in point_list:
            assert point[0] != pt[0], 'Unhashable input.'
            if x & 1:
                point = ec_add(point, pt, FIELD_PRIME)
            x >>= 1
        assert x == 0
    return point

def py_pedersen_hash(*elements: int) -> int:
    return pedersen_hash_as_point(*elements)[0]

def get_hash(*elements: int) -> int:
    return py_pedersen_hash(*elements)

def nonceFromClientId(clientOrderId):
    message = hashlib.sha256()
    message.update(clientOrderId.encode())  # Encode as UTF-8.
    return int(message.digest().hex()[0:8], 16)

class apexHandler:
    def __init__(self,apiKey,secretKey,passPhrase,privateKey,domainName):
        self.apiKey=apiKey
        self.secretKey=secretKey
        self.passPhrase=passPhrase
        self.privateKey=privateKey
        self.domainName=domainName
        self.httpClient=requests.session()
    
    def getRequest(self,endpoint,**kwargs):
        timeStamp=str(int(time.time()*1000))
        params = kwargs
        queryString = ''
        for key in params.keys():
            v = params[key]
            if isinstance(params[key], bool):
                if params[key]:
                    v = 'True'
                else :
                    v = 'False'
            queryString += key + '=' + v + '&'
        queryString = queryString[:-1]
        messageString=""
        endpointQueryString=""
        if len(queryString)>0:
            endpointQueryString=endpoint+"?"+queryString
        else:
            endpointQueryString=endpoint
        messageString=(timeStamp+"GET"+endpointQueryString)
        hashed=hmac.new(
                base64.standard_b64encode(
                    (self.secretKey).encode(encoding='utf-8'),
                ),
                msg=messageString.encode(encoding='utf-8'),
                digestmod=hashlib.sha256,
        )
        signature = base64.standard_b64encode(hashed.digest()).decode()
        headers = {
                'APEX-SIGNATURE': signature,
                'APEX-API-KEY': self.apiKey,
                'APEX-TIMESTAMP': timeStamp,
                'APEX-PASSPHRASE': self.passPhrase
        }
        response = self.httpClient.get(self.domainName+endpointQueryString, headers=headers,verify=False) # You must specify "Content-Type" to "application/x-www-form-urlencoded" if you put query string into request body
        return json.loads(response.text)

    def postRequest(self,endpoint,**kwargs):
        timeStamp=str(int(time.time()*1000))
        params = kwargs
        queryString = ''
        for key in sorted(params.keys()):
        #for key in params.keys():
            v = params[key]
            if isinstance(params[key], bool):
                if params[key]:
                    v = 'True'
                else :
                    v = 'False'
            queryString += key + '=' + str(v) + '&'
        queryString = queryString[:-1]
        messageString=(timeStamp+"POST"+endpoint+queryString)
        hashed=hmac.new(
                base64.standard_b64encode(
                    (self.secretKey).encode(encoding='utf-8'),
                ),
                msg=messageString.encode(encoding='utf-8'),
                digestmod=hashlib.sha256,
        )
        signature = base64.standard_b64encode(hashed.digest()).decode()
        headers = {
                'APEX-SIGNATURE': signature,
                'APEX-API-KEY': self.apiKey,
                'APEX-TIMESTAMP': timeStamp,
                'Content-Type': 'application/x-www-form-urlencoded',
                'APEX-PASSPHRASE': self.passPhrase
        }
        response = self.httpClient.post(self.domainName+endpoint, data=params, headers=headers) # You must specify "Content-Type" to "application/x-www-form-urlencoded" if you put query string into request body
        responseObj={}
        responseObj["network"]=response.raw._original_response._client
        responseObj["apiElapsed"]=int(response.elapsed.microseconds/1000)
        responseObj["text"]=response.text
        responseObj["headers"]=response.headers
        return responseObj

    def initCreateOrder(self,symbol,currency,side):
        resp=self.getRequest("/api/v1/account")
        self.symbol=symbol
        self.limitFee=resp['data']['takerFeeRate']
        self.positionId=resp['data']['positionId']
        self.symbolInfo=list(filter(lambda x:x["symbol"]==symbol,json.loads(self.httpClient.get("https://pro.apex.exchange/api/v1/symbols").text)["data"]["perpetualContract"]))[0]
        self.currencyInfo=list(filter(lambda x:x["id"]==currency,json.loads(self.httpClient.get("https://pro.apex.exchange/api/v1/symbols").text)["data"]["currency"]))[0]
        self.side=side
        self.is_buying_synthetic = side == "BUY"
        self.limit_fee_rounded_4_hash = DECIMAL_CONTEXT_ROUND_UP.quantize(decimal.Decimal(self.limitFee),decimal.Decimal(self.currencyInfo['stepSize']))
        self.synthetic_asset_id = int(
                self.symbolInfo['starkExSyntheticAssetId'],
                16,
        )
        self.collateral_asset_id = int(
                self.currencyInfo['starkExAssetId'],
                16,
        )
        self.asset_id_sell=0
        self.asset_id_buy=0
        self.quantums_amount_sell=0
        self.quantums_amount_buy=0
        if self.is_buying_synthetic:
            self.asset_id_sell = self.collateral_asset_id
            self.asset_id_buy = self.synthetic_asset_id
        else:
            self.asset_id_sell = self.synthetic_asset_id
            self.asset_id_buy = self.collateral_asset_id
        self.ONE_HOUR_IN_SECONDS = 60 * 60
        self.ORDER_SIGNATURE_EXPIRATION_BUFFER_HOURS = 12 * 7 *4
        self.assets_hash = get_hash(get_hash(self.asset_id_sell,self.asset_id_buy),self.collateral_asset_id)

    def createOrder(self,clientOrderId,size,price):
        self.quantums_amount_synthetic = to_quantums_exact(size,self.symbolInfo['starkExResolution'])
        self.size=size
        self.price=price
        if self.is_buying_synthetic:
            self.human_cost = DECIMAL_CONTEXT_ROUND_UP.multiply(decimal.Decimal(size),decimal.Decimal(price))
            self.fee = DECIMAL_CONTEXT_ROUND_UP.multiply(self.human_cost, decimal.Decimal(self.limitFee))
            self.quantums_amount_collateral = to_quantums_round_up(self.human_cost,ASSET_RESOLUTION[COLLATERAL_ASSET])
            self.quantums_amount_sell = self.quantums_amount_collateral
            self.quantums_amount_buy = self.quantums_amount_synthetic
        else:
            self.human_cost = DECIMAL_CONTEXT_ROUND_DOWN.multiply(decimal.Decimal(size),decimal.Decimal(price))
            self.fee = DECIMAL_CONTEXT_ROUND_DOWN.multiply(self.human_cost, decimal.Decimal(self.limitFee))
            self.quantums_amount_collateral = to_quantums_round_down(self.human_cost,ASSET_RESOLUTION[COLLATERAL_ASSET])
            self.quantums_amount_sell = self.quantums_amount_synthetic
            self.quantums_amount_buy = self.quantums_amount_collateral
        self.limit_fee_rounded = DECIMAL_CONTEXT_ROUND_UP.quantize(decimal.Decimal(self.fee),decimal.Decimal(self.currencyInfo['stepSize']))
        self.quantums_amount_fee_decimal = DECIMAL_CONTEXT_ROUND_UP.multiply(self.limit_fee_rounded_4_hash,self.quantums_amount_collateral).to_integral_value(context=DECIMAL_CONTEXT_ROUND_UP)
        expirationEpochSeconds=time.time()+60
        expirationEpoch = math.ceil(float(expirationEpochSeconds) / self.ONE_HOUR_IN_SECONDS) + self.ORDER_SIGNATURE_EXPIRATION_BUFFER_HOURS
        expiration_epoch_hours = math.ceil(float(expirationEpochSeconds) / self.ONE_HOUR_IN_SECONDS) + self.ORDER_SIGNATURE_EXPIRATION_BUFFER_HOURS

        part_1 = self.quantums_amount_sell
        part_1 <<= ORDER_FIELD_BIT_LENGTHS['quantums_amount']
        part_1 += self.quantums_amount_buy
        part_1 <<= ORDER_FIELD_BIT_LENGTHS['quantums_amount']
        part_1 += int(self.quantums_amount_fee_decimal)
        part_1 <<= ORDER_FIELD_BIT_LENGTHS['nonce']
        part_1 += nonceFromClientId(clientOrderId)

        part_2 = 3
        for _ in range(3):
            part_2 <<= ORDER_FIELD_BIT_LENGTHS['position_id']
            part_2 += int(self.positionId)
        part_2 <<= ORDER_FIELD_BIT_LENGTHS['expiration_epoch_hours']
        part_2 += expiration_epoch_hours
        part_2 <<= 17

        timeBeforeHash=int(time.time()*1000)
        signHash=get_hash(get_hash(self.assets_hash,part_1),part_2)
        r, s = py_sign(msg_hash=signHash, priv_key=int(self.privateKey, 16))
        signature=serialize_signature(r, s)
        timeAfterHash=int(time.time()*1000)
        order = {'symbol': self.symbol,'side': self.side,'type': "LIMIT",'timeInForce': "GOOD_TIL_CANCEL",'size': str(self.size),'price': str(self.price),'limitFee': str(self.limit_fee_rounded),'expiration': expirationEpoch * 3600 * 1000,'clientOrderId': clientOrderId,'signature': signature,'reduceOnly':False}
        response=self.postRequest("/api/v1/create-order",**order)
        response["hashCalc"]=timeAfterHash-timeBeforeHash
        return response
