import ast
import unittest

from pyrefine.exceptions import ErrorCallException

from pyrefine.model import VarsContext

from pyrefine.ast_parser import get_invocations_model, get_lambdas_model
from pyrefine.checker import check_invocation_model, check_program, get_checked_lambda_definitions

lambda_def_program = r"""
from pyrefine import *
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
"""


def _unlines(*lines):
    return "\n".join(lines)


class TestLambdaInvoke(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        program_ast = ast.parse(lambda_def_program, "main.py")
        global_ctx, lambda_models = get_checked_lambda_definitions(program_ast)
        cls.lambda_models = lambda_models
        cls.global_ctx = global_ctx

    def test_invokeCheck(self):
        simple_call = _unlines("x = example_mean_pos(5, 7)",
                               "x_er = example_mean_pos(5, -7)")

        self.assertInvocations(simple_call, {'x': True,
                                             'x_er': False})

    def test_simple_comp(self):
        program = _unlines("y = example_mean_pos(example_simple1(2), 1)",
                           "y_er = example_mean_pos(example_simple1(-2), 1)",
                           "y_er2 = example_mean_pos(-example_simple1(2), 1)")

        self.assertInvocations(program, {'y': True,
                                         'y_er': False,
                                         'y_er2': False
                                         })

    def test_nested_calls(self):
        program = _unlines("c = example_diff_sign(example_mean(-3, -1), "
                                "example_mean(1, example_simple1(1) + 5))",
                           "c_er = example_diff_sign(example_mean(-3, -1), "
                                "example_mean_pos(1, example_simple1(-1) + 5))")

        self.assertInvocations(program, {'c': True, 'c_er': False})

    def assertInvocations(self, program, expected):
        program_ast = ast.parse(program, "main.py")
        invocations = get_invocations_model(program_ast, self.lambda_models)
        invocations = dict(invocations)
        self.assertSequenceEqual(invocations.keys(), expected.keys())
        for name, model in invocations.items():
            if expected[name]:
                check_invocation_model(model, self.lambda_models, self.global_ctx, [])
            else:
                with self.assertRaises(ErrorCallException):
                    check_invocation_model(model, self.lambda_models, self.global_ctx, [])


if __name__ == '__main__':
    unittest.main()
