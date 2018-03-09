#!/usr/bin/env python

from pyrefine import *


def main():
    example_simple1 = define_('int -> int', 'a > 0', 'ret > 1',
                               lambda a: 2 if a == 1 else a * 2)

    example_simple2 = define_('int -> int -> int',
                              'a >= 0 and b >= 0',
                              'ret >= 0 and (ret <= a or ret <= b)',
                              lambda a, b: (a + b) // 2)

    example_chain_comp = define_('int -> bool',
                                 '1 <= x <= 2',
                                 'ret == True',
                                 lambda x: 2 <= x*2 <= 4)

    example_simple_wrong = define_('int -> int -> int',
                                   'x > 0 and y > 0',
                                   'ret > 1',
                                   lambda x, y: x*y)


    example_implication = xdefine_('int -> int -> int',
                                   'x > 0 >> y > 0',
                                   'ret > 0',
                                   lambda x, y: x*y)

    example_tup = xdefine_('(int, int, int) -> int -> (int, int)',
                           'a[0] > a[1] and 0 <= i < 3',
                           lambda a, i: (a[i], a[(i + 1) % 3]))

    example_fun = define_('int -> (int -> int) -> int',
                          'forall_({x : int}, f(x) > 0)',
                          'ret > 1',
                          lambda a, f: f(a) + 1)

    example_fun_imp = xdefine_('int -> (int -> int) -> int',
                              'forall_({x : int}, x > 0 >> f(x) > 0) and a > 1',
                              'ret > 1',
                              lambda a, f: f(a) + 1)

    x = example_simple2(5, 7)
    y = example_simple2(example_simple1(2), 1)

    z = example_simple1(2)
    w = example_simple2(z, z)

    a = example_fun(5, example_simple1)


if __name__ == '__main__':
    main()
    print('Done')
