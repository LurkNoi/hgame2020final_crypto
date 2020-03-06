#!/usr/local/bin/sage -python
from sage.all import *
from sage.matrix.berlekamp_massey import berlekamp_massey


N = 128
m = 8
F2 = GF(2)

XOR = lambda s1,s2: bytes([x^y for x,y in zip(s1,s2)])
BIT2BYTE = lambda l: bytes(ZZ(l[::-1], base=2).digits(base=256))[::-1]
BYTE2BIT = lambda b: ZZ(list(b[::-1]), base=256).digits(base=2, padto=8*len(b))[::-1]

cipher = open('msg.enc', 'rb').read()
cipherstream = BYTE2BIT(cipher)
BITS_LENGTH = len(cipherstream)

c = [F2(cipherstream[m*i]) for i in range(2*N)]

Pol = berlekamp_massey(c)

per = 2**Pol.degree() - 1
m_inv = inverse_mod(m, per)
T = companion_matrix(Pol, format='right')
TT = T**m_inv

cc = Matrix(F2, c[:N])
bb = []
for _ in range(2*N):
    bb.append( cc[0, 0] )
    cc = cc*TT
fill = bb[:N]

gg = berlekamp_massey(bb)
key = gg.coefficients(sparse=False)[:-1]

keystream = lfsr_sequence(key, fill, BITS_LENGTH)
KEY = BIT2BYTE(keystream)

msg = XOR(cipher, KEY)
print('msg:', msg.decode())