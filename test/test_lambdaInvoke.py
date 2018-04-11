import ast
import unittest

from pyrefine.exceptions import ErrorCallException

from pyrefine.checker import check_program

lambda_def_program = r"""
from pyrefine import *
def main():
    define_('int', 'True', 'True')
    example_simple1 = define_('int -> int', 'a >= 0', 'ret > 0',
                               lambda a: 1 if a == 0 else a * 2)
    
    example_simple2 = define_('int -> int', 'True', 'ret > a',
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
    
    example_diff_sign = define_('int -> int -> int',
                                'a*b < 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)
    {}
    return 0
"""


def _unlines(*lines):
    return "\n".join(lines)


class TestLambdaInvoke(unittest.TestCase):

    def assertCorrect(self, program, func_name='main'):
        res = check_program(lambda_def_program.format(program))
        self.assertIn(func_name, res)

    def assertErrCall(self, program, error_call_name):
        with self.assertRaises(ErrorCallException) as e:
            check_program(lambda_def_program.format(program))
        self.assertEqual(e.exception.name, error_call_name)

    def test_invokeCheck(self):
        self.assertCorrect("x = example_mean_pos(5, 7)")
        self.assertErrCall("x = example_mean_pos(5, -7)", 'example_mean_pos')

    def test_simple_comp(self):
        self.assertErrCall(
            "y_er = c_(example_mean_pos(example_simple1(-2), 1))", 'example_simple1')
        self.assertErrCall(
            "y_er2 = c_(example_mean_pos(-example_simple1(2), 1))", 'example_mean_pos')

    def test_nested_calls(self):
        self.assertCorrect("c = example_diff_sign(example_mean(-3, -1), "
                                "example_mean(1, example_simple1(1) + 5))")

        self.assertErrCall("c_er = example_diff_sign(example_mean(-3, -1), "
                            "example_mean_pos(1, example_simple1(-1) + 5))",
                           "example_simple1")


    def test_invokeCheck_with_type(self):
        self.assertCorrect("x = c_('int', example_mean_pos(5, 7))")
        self.assertErrCall("x = c_('int', example_mean_pos(5, -7))", 'example_mean_pos')

