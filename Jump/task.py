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


print('g:', g)
# g: x^128 + x^125 + x^123 + x^122 + x^121 + x^117 + x^116 + x^111 + x^109 + x^104 + x^101 + x^100 + x^98 + x^97 + x^94 + x^93 + x^91 + x^87 + x^79 + x^78 + x^77 + x^76 + x^75 + x^74 + x^72 + x^69 + x^66 + x^64 + x^63 + x^62 + x^61 + x^59 + x^58 + x^57 + x^54 + x^53 + x^52 + x^47 + x^46 + x^45 + x^44 + x^43 + x^41 + x^40 + x^33 + x^32 + x^31 + x^28 + x^27 + x^26 + x^24 + x^21 + x^20 + x^16 + x^14 + x^13 + x^12 + x^10 + x^8 + x^7 + x^5 + x^2 + 1
# Actually, `g` is not necessary to solve this challenge.
