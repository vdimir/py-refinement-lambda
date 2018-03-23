#!/usr/bin/env python

from pyrefine import *


def main():

    # example_tup = xdefine_('(int, int, int) -> int -> (int, int)',
    #                        'a[0] > a[1] and 0 <= i < 3',
    #                        lambda a, i: (a[i], a[(i + 1) % 3]))

    example1 = define_('int -> int -> int', 'a >= b', 'ret >= 0',
                       lambda a, b: a - b)
    #
    example_lam_outer = define_('int -> int', 'a > 1', 'ret >= 1',
                                lambda a: example1(a-1, 1) + 1)

    example_simple1 = define_('int -> int', 'a >= 0', 'ret > 0',
                              lambda a: 1 if a == 0 else a * 2)

    example_simple2 = define_('int -> int', 'a > -10', 'ret > -10',
                              lambda a: a + 1)

    example_mean = define_('int -> int -> int',
                           'True',
                           '(ret <= a or ret <= b) and (a <= ret or b <= ret)',
                           lambda a, b: (a + b) // 2)

    example_mean_pos = define_('int -> int -> int',
                               'a > 0 and b > 0',
                               '(ret <= a or ret <= b) and (0 <= ret or 0 <= ret)',
                               lambda a, b: (a + b) // 2)

    example_imp = define_('int -> int -> int',
                          '(x > 0) >> (y > 1)',
                          'ret > x or ret <= 0 ',
                          lambda x, y: x * y)

    # example_fun = define_('int -> (int -> int) -> int',
    #                       'forall_({x : int}, f(x) > 0)',
    #                       'ret > 1',
    #                       lambda a, f: f(a) + 1)

    # example_fun_imp = define_('int -> (int -> int) -> int',
    #                           'forall_({x : int}, (x > 0) >> (f(x) > 0)) and a < -2',
    #                           'ret > 1',
    #                           lambda a, f: f(-a) + 1)

    example_diff_sign = define_('int -> int -> int',
                                'a*b < 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)

    example_simple3 = define_('int -> int', 'True', 'ret > a',
                              lambda a: a + 1)

    example_simple4 = define_('bool -> bool -> bool', 'True', 'ret == (a >> b)',
                              lambda a, b: b if a else True)


    y = example_mean_pos(example_simple1(2), 1)
    c = example_diff_sign(example_mean(-3, -1), example_mean(1, example_simple1(1) + 5))

    # TODO should be error
    # a = example_fun(5, example_simple1)
    # b = example_simple1(example_fun(5, example_simple1))
    # a_err = example_fun(1, example_simple2)


if __name__ == '__main__':
    main()
    print('Done')
