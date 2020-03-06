#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import z3
import pycryptosat

from task_python import *


class LFSR_z3:

    def __init__(self, nbits, key):
        self.nbits = nbits
        self.slvr = z3.Goal()
        self.init = z3.BitVec('init', nbits)
        tmp = z3.BitVec('tmp', nbits) 
        # make sure Goal() start with `init` (at step 2)
        for i in range(nbits):
            self.slvr.add(
                z3.Extract(i, i, tmp)
                == z3.Extract(i, i, self.init)
            )
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

    def write(self):
        t = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')
        subgoal = t(self.slvr)
        assert len(subgoal) == 1
        open('cnf.dimacs', 'w').write(subgoal[0].dimacs())



def frombools(bs):
    b = ''
    for bi in bs:
        if bi:
            b = '1' + b
        else:
            b = '0' + b
    return int(b, 2)


def solve(nbits):
    sat = pycryptosat.Solver(threads=4)

    with open('cnf.dimacs', 'r') as f:
        print(f.readline().strip())
        for line in f:
            if line.startswith('c'):
                print('comment, break')
                break
            sat.add_clause(list(map(int, line[:-3].split())))

    is_sat, res = sat.solve()
    if not is_sat:
        raise ValueError('UNSAT')
    else:
        init = frombools(res[1:2*nbits+1][::2])
        print(f"{init:0{nbits}b}")
        return init



if __name__ == '__main__':

    CIPHER = open('msg.enc', 'rb').read()

    N = 128
    poly = 0xa5ae8cb9c0df0e77a4bf01166c850c74
    smt = LFSR_z3(N, poly)

    # lfsr = LFSR(poly, 0xa5ae8cb9c0df0e77a4bf01166c850c74, N)
    # for i in range(2*8*N):
    #     if i % 8 == 0:
    #         smt.get(lfsr.next())
    #     else:
    #         lfsr.next()
    #         smt.step()

    print('collecting bits...')
    for c in CIPHER:
        # print(c, end='\r')
        bit = c >> 7
        smt.get(bit)
        for _ in range(7):
            smt.step()
    
    print('converting to cnf...')
    smt.write()
    print('solving...')
    # print(poly)
    # print(f"{poly:0{N}b}")
    print(solve(N))
