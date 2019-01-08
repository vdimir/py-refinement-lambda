#!/usr/bin/env python

from pyrefine import *

# def gcd(x, y):
#     define_('int -> int -> int',
#             'x > 0 and y > 0',
#             'ret > 0')
#     t = c_('int', 0)
#     while x != y:
#         loop_('x > 0 and y > 0', 'x + y')
#         if x > y:
#             y, x = x, y
#         assert y > x
#         y = y - x
#     assert x == y
#     return y


def foo(x,y):
    define_('float -> float -> float', 
            'x > 0', 
            'ret > 2')
    abs_ = define_('float -> float', 'True', 
                '(x >= 0) >> (ret == x) and (x < 0) >> (ret == -x)',
                lambda x: x if x > 0 else -x)
    y = abs_(y)
    assert y >= 0
    y = y + 1
    assert y >= 1
    f = define_('int -> int -> int', 'n != 0', 'abs_(ret) <= abs_(n)',
                 lambda x, n: x % n)
    f2 = define_('float -> float', 'a > 0', 'ret > a',
              lambda a: x + a)
    return f2(2)

# def main():
#     define_('int', 'True', 'True')

#     a = c_('int', 120)
#     b = c_('int', 56)
#     c = gcd(a, b)
#     print("GCD({}, {}) = {}".format(a, b, c))

#     return 0

# if __name__ == '__main__':
#     main()
