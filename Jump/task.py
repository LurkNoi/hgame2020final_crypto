#!/usr/local/bin/sage -python
from sage.all import *
from secret import PLAINTEXT

N = 128
BITS_LENGTH = 8*len(PLAINTEXT)

XOR = lambda s1,s2: bytes([x^y for x,y in zip(s1,s2)])
BIT2BYTE = lambda l: bytes(ZZ(l[::-1], base=2).digits(base=256))[::-1]

R = PolynomialRing(GF(2), 'x')
g = R.irreducible_element(N, 'random')
key = g.coefficients(sparse=False)[:-1]
fill = ZZ( randint(2**(N-1), 2**N-1) ).bits()

keystream = lfsr_sequence(key, fill, BITS_LENGTH)
KEY = BIT2BYTE(keystream)
cipher = XOR(PLAINTEXT, KEY)

open('msg.enc', 'wb').write(cipher)

