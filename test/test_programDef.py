import unittest

from pyrefine.checker import check_program

program = """
#!/usr/bin/env python

from pyrefine import *


def simple_swap(x, y):
    define_('int -> int -> int',
            'x > 0 and y > 0 and x != y',
            'ret > 0')

    if y > x:
        x, y = y, x
    return x - y


def simple_swap1(x, y):
    define_('int -> int -> int',
            'x > 0 and y > 0 and x != y',
            'ret > 0')
    t = c_('int', 0)

    if y > x:
        t = x
        x = y
        y = t
    return x - y


def using_lam(x, y):
    define_('int -> int -> int', 'x < 0', 'ret > y')

    neg = define_('int -> int', 'True', 'ret * x <= 1',
                  lambda x: -x)

    example_simple1 = define_('int -> int', 'a >= 0', 'ret > 0',
                              lambda a: simple_swap(1, 8) if a == 0 else a * 2)

    t = example_simple1(neg(x) + 1)
    return y + t


def gcd2(x, y):
    define_('int -> int -> int',
            'x > 0 and y > 0',
            'ret > 0')
    t = c_('int', 0)
    while x != y:
        loop_('x > 0 and y > 0', 'x + y')
        if x > y:
            y, x = x, y
        y = y - x
    return y


def simple(x, y):
    define_('int -> int -> int',
            'x > 0 and y > 0',
            'ret == x + y')
    a = c_('int', x)
    res = c_('int', 0)
    res = a + y
    return res


def simple_if(x, y):
    define_('int -> int -> int',
            'x != 0',
            'ret > 0')
    a = c_('int', 0)
    a = x
    if x < 0:
        a = -x
    return a


def simple_if2(x, y):
    define_('int -> int -> int',
            'y >= 0 and x >= 0',
            'ret > 0')
    a = c_('int', 1)
    if y > x:
        a = y
    b = c_('int', y)
    return a + b


def simple_if3(x, y):
    define_('int -> int -> bool',
            'y >= 0',
            'ret == True')
    if x > y:
        x = y
    return x <= y


def simple_if_else(x, y):
    define_('int -> int -> int',
            'True',
            'ret > 0')
    a = c_('int', 0)
    if x > y:
        a = x - y
    else:
        a = y - x + 1
    return a


def simple_while(x):
    define_('int ->  int',
            'x >= 0',
            'ret >= 0')
    s = c_('int', 0)
    while x != 0:
        loop_('x >= 0 and s >= 0', 'x')
        s = s + x
        x = x - 1
    return s


def gcd(x, y):
    define_('int -> int -> int',
            'x > 0 and y > 0',
            'ret > 0')
    while x != y:
        loop_('x > 0 and y > 0', 'x + y')
        if x < y:
            y = y - x
        else:
            x = x - y
    return y

"""


class TestProgramDef(unittest.TestCase):
    def test_all(self):
        res = check_program(program)
        for func_name in ['simple_swap', 'simple_swap1', 'using_lam', 'gcd2',
                            'simple', 'simple_if', 'simple_if2', 'simple_if3',
                            'simple_if_else', 'simple_while', 'gcd']:
            self.assertIn(func_name, res)




