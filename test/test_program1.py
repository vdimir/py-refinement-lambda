import unittest

from pyrefine.checker import check_program

from pyrefine.exceptions import *


program1 = r"""
#!/usr/bin/env python

from pyrefine import *

def main():
    define_('int', 'True', 'ret == 0')

    example_imp0 = define_('bool -> bool -> bool', 'True', 'ret == (a >> b)',
                              lambda a, b: b if a else True)

    example1 = define_('int -> int -> int', 'a >= b', 'ret > 0',
                       lambda a, b: 1 if example_imp0(b > 5, a > 5) else 0)

    example_const = define_('int', 'True', 'ret == 666',
                            lambda: 666)

    example_lam_outer = define_('int -> int', 'a > 1', 'ret >= 1',
                                lambda a: example1(a+example_const(), 1) + 1)

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
                               '(ret <= a or ret <= b) and (0 <= ret)',
                               lambda a, b: (a + b) // 2)

    example_imp = define_('int -> int -> int',
                          '(x > 0) >> (y > 1)',
                          'ret > x or ret <= 0 ',
                          lambda x, y: x * y)

    example_diff_sign = define_('int -> int -> int',
                                'a*b < 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)

    example_simple3 = define_('int -> int', 'True', 'ret > a',
                              lambda a: a + 1)

    example_simple4 = define_('bool -> bool -> bool', 'True', 'ret == (a >> b)',
                              lambda a, b: b if a else True)

    y = example_mean_pos(example_simple1(2), 1)
    c = c_(example_diff_sign(example_mean(-3, -1), example_mean(1, example_simple1(1) + 5)))

    a = c_('int', -5)
    zero = c_('int', a + 5)

    y1 = c_('int', example1(example_simple1(zero), -y))
    
    q = c_('int', -666)
    z = c_('int', example_mean_pos(1 if y1 <= 0 else y1, 1) + 1)

    example_simple_global_var = define_('int -> int', 'True', 'ret >= 0',
                                        lambda x: x if x > 0 else z)
    return q + 666


if __name__ == '__main__':
    main()
    print('Done')

"""


class TestProgram1(unittest.TestCase):
    def test_1(self):
        res = check_program(program1)
        self.assertIn('main', res)
