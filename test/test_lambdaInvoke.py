import ast
import unittest

from pyrefine.ast_parser import get_invocations_model
from pyrefine.checker import check_all_lambdas, check_invocation_model

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
"""


def _unlines(*lines):
    return "\n".join(lines)


class TestLambdaInvoke(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        program_ast = ast.parse(lambda_def_program, "main.py")
        lambda_models = check_all_lambdas(program_ast)

        cls.lambda_models = dict(map(lambda m: (m.func_name, m), lambda_models))

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

    # @unittest.skip
    # def test_higher_order(self):
    #     program = _unlines("a = example_fun(5, example_simple1)",
    #                        "b = example_simple1(example_fun(5, example_simple1))",
    #                        "a_err = example_fun(1, example_simple2)")
    #
    #     self.assertInvocations(program, {'a': True, 'b': True, 'a_err': False})

    def assertInvocations(self, program, expected):
        program_ast = ast.parse(program, "main.py")
        invocations = get_invocations_model(program_ast, self.lambda_models)
        invocations = dict(invocations)
        self.assertSequenceEqual(invocations.keys(), expected.keys())
        for name, model in invocations.items():
            counterexample = check_invocation_model(model, self.lambda_models)
            is_valid = counterexample is None
            self.assertEqual(is_valid, expected[name])


if __name__ == '__main__':
    unittest.main()
