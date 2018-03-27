import unittest

from pyrefine.exceptions import CheckerException

from pyrefine.checker import check_program

program_base = r"""
#!/usr/bin/env python

from pyrefine import *

example_global = define_('int -> int -> int', 'a > 0', 'ret > b',
                   lambda a, b: a + b)

def main():
    example1 = define_('int -> int -> int', 'a >= b', 'ret >= 0',
                       lambda a, b: example_global(a - b + 1, 1))

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

    # example_global = define_('bool -> bool -> bool', 'True', 'ret == (a >> b)',
    #                           lambda a, b: b if a else True)
    y1 = c_('int', example1(example_simple1(zero), -y))
    z = c_('int', example_mean_pos(1 if y1 <= 0 else y1, 1) + 1)

    q = c_('int', -666)
    example_simple_global_var = define_('int -> int', 'True', 'ret >= 0',
                                        lambda x: x if x > 0 else z)


if __name__ == '__main__':
    main()
    print('Done')

"""


def _unlines(*lines):
    return "\n".join(lines)


class TestProgram(unittest.TestCase):

    def test_1(self):
        self.assertProgramSafe(program_base)

    def test_redefine(self):
        # constant
        with self.assertRaises(CheckerException) as e:
            check_program(_unlines("x = c_('int', 5)",
                                                    "x = c_('int', -5)"))
        self.assertEqual(e.exception.reason, "Variable `x` already defined.")

        # function
        with self.assertRaises(CheckerException) as e:
            check_program(_unlines(
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)",
                "x = define_('int -> int', 'True', 'True', lambda x: x + 6)"))
        self.assertEqual(e.exception.reason, "Variable `x` already defined.")

        # mixed
        with self.assertRaises(CheckerException) as e:
            check_program(_unlines(
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)",
                "x = 5"))
        self.assertEqual(e.exception.reason, "Variable `x` already defined.")

    def test_namehiding(self):
        program = _unlines("x = c_('int', -5)",
                           "f = define_('int -> int', 'x > 0', 'ret > 1',"
                                "lambda x: x + 1)")
        check_program(program)

    def test_globalFuncInCond(self):
        program = _unlines("f = define_('int', 'True', 'ret < 0',  lambda: -5)",
                           "g = define_('int -> int', 'x > -f()', 'ret > 1',"
                                "lambda x: x + 1)")
        check_program(program)

        program = _unlines("abs_ = define_('int -> int', 'True', "
                                "'(x >= 0) >> (ret == x) and (x < 0) >> (ret == -x)',"
                                "lambda x: x if x > 0 else -x)",
                           "g = define_('int -> int', 'True', 'abs_(ret) > 1',"
                                "lambda x: x*x + 2)")
        check_program(program)


    def assertProgramSafe(self, program):
        counterexample = check_program(program)
        self.assertIsNone(counterexample)


if __name__ == '__main__':
    unittest.main()
