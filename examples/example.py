#!/usr/bin/env python

import foo


def main():
    example_simple1 = _define('int -> int', 'a > 0', 'ret > 1',
                               lambda a: 2 if a == 1 else a * 2)

    example_simple2 = _define('int -> int -> int',
                              'a >= 0 and b >= 0',
                              'ret >= 0 and (ret <= a or ret <= b)',
                              lambda a, b: (a + b) // 2)

    example_chain_comp = _define('int -> bool',
                                  '1 <= x <= 2',
                                  'ret == True',
                                  lambda x: 2 <= x*2 <= 4)


    example_tup = x_define('(int, int, int) -> int -> (int, int)',
                           'a[0] > a[1] and 0 <= i < 3',
                           lambda a, b: (a[i], a[(i + 1) % 3]))

    # 'forall(x, f(x) > 0)',
    example_fun = x_define('int -> fun(int, int) -> int',
                           'lambda x: f(x) > 0',
                           'ret > 1',
                           lambda a, f: f(a) + 1)

    x = example_simple2(5, 7)
    y = example_fun(5, example_simple1)


if __name__ == '__main__':
    main()
