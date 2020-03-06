#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os


XOR = lambda s1,s2: bytes([x^y for x,y in zip(s1,s2)])


def n2b(n: int, blocksize: int = 0) -> bytes:
    s = n.to_bytes((n.bit_length() + 7) // 8, 'big')

    if blocksize > 0 and len(s) % blocksize:
        s = (blocksize - len(s) % blocksize) * b'\x00' + s
    return s


def b2n(s: bytes) -> int:
    return int.from_bytes(s, 'big')


class LFSR:

    def __init__(self, fill, key, nbits):
        self.nbits = nbits
        self.mask = (1 << nbits) - 1
        self.state = fill & self.mask
        self.poly = key & self.mask

    def next(self):
        o = self.state >> (self.nbits - 1)
        state_n = (self.state << 1) & self.mask 
        i = self.state & self.poly & self.mask 
        next_bit = 0
        while i:
            next_bit ^= (i & 1)
            i = i >> 1
        state_n ^= next_bit
        self.state = state_n

        return o

    def gen(self, length):
        out = b''
        for _ in range(length):
            o = self.next()
            for i in range(7):
                o <<= 1
                o |= self.next()
            out += bytes([o])

        return out

    def encrypt(self, data):
        k = self.gen(len(data))
        return XOR(data, k)



if __name__ == '__main__':
    from secret import PLAINTEXT

    N = 128

    key = 0xa5ae8cb9c0df0e77a4bf01166c850c74
    fill = b2n(os.urandom(N // 8))
    lfsr = LFSR(fill, key, N)

    CIPHERTEXT = lfsr.encrypt(PLAINTEXT)
    open('msg.enc', 'wb').write(CIPHERTEXT)
