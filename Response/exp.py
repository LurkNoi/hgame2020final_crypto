#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import binascii
import re

from Crypto.Util.Padding import pad
from pwn import *

# context.log_level = 'debug'

LOCAL = True
if LOCAL:
    HOST, PORT = '127.0.0.1', 1234
else:
    HOST, PORT = '47.98.192.231', 25159


def xor(a, b):
    return bytes([x^y for x,y in zip(a,b)])


def blocks(data):
    bs = [bytes(data[16*i : 16*(i+1)])
        for i in range(len(data)//16)]
    return bs


def enc(data):
    r = remote(HOST, PORT)

    r.sendlineafter('Who are you? ', 'Alice')
    r.sendlineafter('challenge (in hex): ', '00'*10)
    res = r.recvregex(r'Response\s\(in\shex\):\s\w+\n').decode()
    hex_ct = re.search(r'Response\s\(in\shex\):\s(\w+)\n', res).groups()[0]
    ct = binascii.unhexlify(hex_ct)
    c0 = blocks(ct)[1]
    r.sendlineafter('response (in hex): ', '00'*32)

    m1 = xor(data, c0)
    r.sendlineafter('Who are you? ', 'Alice')
    r.sendlineafter('challenge (in hex): ', '00'*10+m1.hex())
    res = r.recvregex(r'Response\s\(in\shex\):\s\w+\n').decode()
    hex_ct = re.search(r'Response\s\(in\shex\):\s(\w+)\n', res).groups()[0]
    ct = binascii.unhexlify(hex_ct)
    c1 = blocks(ct)[2]

    r.close()

    return c1


r = remote(HOST, PORT)
r.sendlineafter('Who are you? ', 'Alice')
r.sendlineafter('challenge (in hex): ', '00'*16)
res = r.recvregex(r'Challenge\s\(in\shex\):\s\w{32}\n').decode()
hex_challenge = re.search(r'Challenge\s\(in\shex\):\s(\w{32})\n', res).groups()[0]
challenge = binascii.unhexlify(hex_challenge)

msg = pad(b'Alice'+challenge, 16)
m0, m1 = blocks(msg)
iv = b'\x00' * 16

c0 = enc(m0)
c1 = enc(xor(c0, m1))
response = iv + c0 + c1

r.sendlineafter('response (in hex): ', response.hex())
f = r.recvregex('hgame{.+}').decode()
flag = re.search('(hgame{.+})', f).groups()[0]

log.info(f"flag: {flag}")
r.close()
