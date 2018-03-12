#!/usr/bin/env python

from pyrefine import *


def main():

    # example_tup = xdefine_('(int, int, int) -> int -> (int, int)',
    #                        'a[0] > a[1] and 0 <= i < 3',
    #                        lambda a, i: (a[i], a[(i + 1) % 3]))

    example_simple2 = define_('int -> int', 'True', 'ret > a',
                              lambda a: a + 1)

    example_fun = define_('int -> (int -> int) -> int',
                          'forall_({x : int}, f(x) > 0)',
                          'ret > 1',
                          lambda a, f: f(a) + 1)

    a = example_fun(-5, example_simple2)
    print(a)

if __name__ == '__main__':
    main()
    print('Done')
