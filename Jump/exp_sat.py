#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import random
import time
import signal
from functools import reduce

import z3
import pycryptosat
from task_python import *


class LFSR_z3:

    def __init__(self, nbits, key):
        self.nbits = nbits
        self.slvr = z3.Solver()
        self.init = z3.BitVec('init', nbits)
        self.state = self.init
        self.poly = z3.BitVecVal(key, nbits)
        self.zero = z3.BitVecVal(0, nbits)
        self.one = z3.BitVecVal(1, nbits)

    def step(self):
        o = z3.Extract(self.nbits-1, self.nbits-1, self.state)
        state_n = self.state << 1
        i = self.state & self.poly
        next_bit = self.zero
        for _ in range(self.nbits):
            next_bit ^= (i & self.one)
            i = z3.LShR(i, 1)
        state_n ^= next_bit
        self.state = state_n

        return o

    def get(self, bit):
        bit = z3.BitVecVal(bit, 1)
        o = self.step()
        self.slvr.add(o == bit)

    def solve(self, verify=False):
        is_sat = self.slvr.check()
        if is_sat == z3.unsat:
            raise ValueError('UNSAT')

        elif not verify:
            print(self.slvr.model())

        else:
            pass



def tobits(a, nbits):
    b = [((a >> i) & 1) for i in range(nbits)]
    return b
 
def frombits(b):
    nbits = len(b)
    a = sum([(b[i] << i) for i in range(nbits)])
    return a

def toidx(a, nbits):
    b = [(i+1) for i in range(nbits) 
         if ((a >> i) & 1) == 1]
    return b

def fromidx(b):
    a = sum([(1 << b_i) for b_i in b])
    return a

def frombools(bs):
    b = ''
    for bi in bs:
        b += '1' if bi else '0'
    return int(b[::-1], 2)

def tobools(a, nbits):
    l = [bool((a >> i) & 1) for i in range(nbits)]
    return l

def and_lst(a, b):
    return [a[idx-1] for idx in b]

def xor_lst(a, b):
    a = a.copy()
    for bi in b:
        if bi in a:
            a.remove(bi)
        else:
            a.append(bi)
    return a


class LFSR_z3b:
    """Imply with z3 BoolVector"""
    def __init__(self, nbits, pol):
        self.nbits = nbits
        self.slvr = z3.Solver()
        self.init = z3.BoolVector('init', nbits)
        self.state = self.init
        self.pol = tobools(pol, nbits)

    def _reduce_xor(self, a):
        return reduce(z3.Xor, a)

    def _and(self, a, b):
        assert len(a) == len(b)
        c = list(map(z3.And, zip(a,b)))
        return c

    def step(self):
        state_n = self.state[:-1]
        o = self.state[-1]
        i = self._and(self.state, self.pol)
        next_bit = self._reduce_xor(i)
        state_n.insert(0, next_bit)
        self.state = state_n
        return o

    def get(self, bit):
        o = self.step()
        self.slvr.add(o == (bit==1))

    def solve(self, verify=False):
        is_sat = self.slvr.check()
        if is_sat == z3.unsat:
            print('unsat')
            return None

        elif not verify:
            print(self.slvr.model())
            return None
        else:
            model = self.slvr.model()
            init = ''
            for i in range(self.nbits):
                is_sat = self.slvr.check(
                    z3.Not(model.eval(self.init[i]))
                )
                if is_sat == z3.unsat:
                    init = ('1' if model.eval(self.init[i])
                        else '0') + init
                else:
                    init = '.' + init

            if '.' not in init:
                print(f"init = {int(init, 2)}")
            else:
                print(init)



class LFSR_sat:

    def __init__(self, nbits, pol, threads=4):
        self.nbits = nbits
        self.state = [[i+1] for i in range(nbits)]
        self.state.insert(0, None)
        self.pol = toidx(pol, nbits)
        self.slvr = pycryptosat.Solver(threads=threads)

    def _and(self):
        return [self.state[idx] for idx in self.pol]

    def _reduce_xor(self, *args):
        if len(args) == 1:
            return args[0]
        o = args[0]
        for i in range(1, len(args)):
            o = xor_lst(o, args[i])
        return o

    def step(self):
        o = self.state[-1]
        i = self._and()
        next_bit = self._reduce_xor(*i)
        state_n = [None] * (self.nbits+1)
        state_n[1] = next_bit
        for idx in range(2, self.nbits+1):
            state_n[idx] = self.state[idx-1]
        self.state = state_n
        return o.copy()

    def get(self, bit):
        o = self.step()
        self.slvr.add_xor_clause(o, bit==1)

    def solve(self, verify=True):
        is_sat, res = self.slvr.solve()
        if not is_sat:
            raise ValueError('UNSAT')

        elif verify:
            state = ''
            for i in range(self.nbits):
                bit = res[i+1]
                if bit:
                    is_sat = self.slvr.solve([-(i+1)])[0]
                else:
                    is_sat = self.slvr.solve([i+1])[0]
                if is_sat:
                    state = '.' + state
                else:
                    state = str(int(bit)) + state
                    
            if '.' in state:
                print('not unique')
                print(state)

        return frombools(res[1:])



if __name__ == '__main__':
    CIPHER = open('msg.enc', 'rb').read()

    N = 128
    poly = 0xa5ae8cb9c0df0e77a4bf01166c850c74
    slvr = LFSR_sat(N, poly)

    print('collenting...')
    for c in CIPHER:
        bit = c >> 7
        slvr.get(bit)
        for _ in range(7):
            slvr.step()
        
    print('Solving...')
    s = time.time()
    fill = slvr.solve()
    print(f'found fill: {fill:032x}')
    e = time.time()
    print(f'finished in {e-s:.3f} s\n')

    print('decrypt for flag')
    lfsr = LFSR(fill, poly, N)
    PLAINTEXT = lfsr.encrypt(CIPHER)
    print(PLAINTEXT.decode())
