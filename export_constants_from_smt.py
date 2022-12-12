#!/usr/bin/env python3

import sys
import z3
import os


def all_values(func_name):
    s = z3.Solver()
    s.from_string(open('constants.smt', 'r').read() +
                  f'\n(declare-const row Int)\n(declare-const val Int)\n(assert ({func_name} row val))')
    row = z3.Int('row')
    val = z3.Int('val')
    for i in range(2097152):
        # Without the push and pop, this is much slower.
        # TODO: maybe report a Z3 bug?
        s.push()
        s.check(row == i)
        yield s.model()[val]
        s.pop()


def output_function(func_name):
    try:
        os.mkdir('constants_from_smt')
    except:
        pass
    out = open(f'constants_from_smt/{func_name}.json', 'w')
    vals = all_values(func_name)
    out.write(f'["{next(vals)}')
    for val in vals:
        out.write(f',"{val}"')
    out.write("]\n")


def print_values(func_name):
    for i, val in enumerate(all_values(func_name)):
        print(i, val, sep=': ')


if __name__ == '__main__':
    output_function(sys.argv[1])
    # print_values(sys.argv[1])
