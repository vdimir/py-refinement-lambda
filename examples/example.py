#!/usr/bin/env python

from pyrefine import *


def main():

    # example_tup = xdefine_('(int, int, int) -> int -> (int, int)',
    #                        'a[0] > a[1] and 0 <= i < 3',
    #                        lambda a, i: (a[i], a[(i + 1) % 3]))

    example_simple1 = define_('int -> int', 'a >= 0', 'ret > 0',
                               lambda a: 1 if a == 0 else a * 2)


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

    example_fun = define_('int -> (int -> int) -> int',
                          'forall_({x : int}, f(x) > 0)',
                          'ret > 1',
                          lambda a, f: f(a) + 1)

    example_fun_imp = define_('int -> (int -> int) -> int',
                              'forall_({x : int}, (x > 0) >> (f(x) > 0)) and a < -2',
                              'ret > 1',
                              lambda a, f: f(-a) + 1)

    example_diff_sign = define_('int -> int -> int',
                                'a*b < 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)
    x = example_mean_pos(5, 7)

    y = example_mean_pos(example_simple1(2), 1)
    #
    a = example_fun(5, example_simple1)
    b = example_simple1(example_fun(5, example_simple1))

    c = example_diff_sign(example_mean(-3, -1), example_mean(1, example_simple1(1)+5))

    x_wrong = example_mean_pos(-5, 7)
    c_wrong = example_diff_sign(example_mean(-3, -1), example_mean_pos(1, example_simple1(-1)+5))
    c_wrong2 = example_diff_sign(-1, example_mean_pos(-3, 1))


if __name__ == '__main__':
    main()
    print('Done')
