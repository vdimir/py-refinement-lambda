import ast
import unittest

from pyrefine.checker import get_checked_lambda_definitions, VarsContext

from pyrefine.checker.check_program import check_program, check_lambda
from pyrefine.exceptions import ParseException, LambdaDefinitionException
from pyrefine.ast_parser.lambda_parser import get_lambdas_model

program_simple = r"""
def main():
    example_simple1 = define_('int -> int', 'a > 0', 'ret > 1',
                               lambda a: 2 if a == 1 else a * 2)

    example_simple2 = define_('int -> int -> int',
                              'a >= 0 and b >= 0',
                              'ret >= 0 and (ret <= a or ret <= b) and (a <= ret or b <= ret)',
                              lambda a, b: (a + b) // 2)

    example_chain_comp = define_('int -> bool',
                                  '1 <= x <= 2',
                                  'ret == True',
                                  lambda x: 2 <= x*2 <= 4)

    example_simple_wrong = define_('int -> int -> int',
                                  'x > 0 and y > 0',
                                  'ret > 1',
                                  lambda x, y : x*y)

    example_diff_sign = define_('int -> int -> int',
                                'a*b <= 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)

    x = example_simple2(5, 7)
    x = example_simple2(example_simple1(2), 1)
    z = 10
    x = example_simple2(example_simple1(z), z)

if __name__ == '__main__':
    main()
    print('Done')

"""


def _unlines(*lines):
    return "\n".join(lines)


class TestLambdaChecker(unittest.TestCase):

    def test_lambda_simple(self):
        program_ast = ast.parse(program_simple, "main.py")

        models = get_lambdas_model(program_ast)

        models = dict(map(lambda m: (m.func_name, m), models))

        all_names = ['example_simple1', 'example_simple2',
                     'example_chain_comp', 'example_diff_sign', 'example_simple_wrong']
        self.assertSetEqual(set(all_names), set(models.keys()))

        global_ctx = VarsContext()
        for n in ['example_simple1', 'example_simple2', 'example_chain_comp']:
            check_lambda(models[n], global_ctx)
            self.assertIsNotNone(global_ctx.functions.get(n))

        with self.assertRaises(LambdaDefinitionException):
            check_lambda(models['example_simple_wrong'])

    @unittest.skip
    def test_func_arg(self):
        program_safe = """example_fun = define_('int -> (int -> int) -> int',
                                  'forall_({x : int}, f(x) > 0)',
                                  'ret > 1',
                                  lambda a, f: f(a) + 1)"""

        program_unsafe = """example_fun = define_('(int -> int) -> bool',
                                  'forall_({x : int}, f(x) > 0)',
                                  'ret',
                                  lambda f: f(0) > 1)"""

        self.assertProgramSafe(program_safe)
        self.assertProgramUnSafe(program_unsafe)

    @unittest.skip
    def test_implication(self):
        program = """example_fun_imp = define_('int -> (int -> int) -> int',
                                  'forall_({x : int}, (x > 0) >> (f(x) > 0)) and ~(a > -2)',
                                  'ret > 1',
                                  lambda a, f: f(-a) + 1)""" + \
                  """\n\nexample_imp = define_('int -> int -> int',
                                       '(x > 0) >> (y > 1)',
                                       'ret > x or ret <= 0 ',
                                       lambda x, y: x * y)"""

        program1_wrong = """example_fun_imp = define_('int -> (int -> int) -> int',
                                  'forall_({x : int}, (x > 0) >> (f(x) > 0))',
                                  'ret > 1',
                                  lambda a, f: f(-a) + 1)"""

        self.assertProgramSafe(program)
        self.assertProgramUnSafe(program1_wrong)

    def test_parse_exception(self):

        program = ("ex_imp = define_('bool -> bool -> bool', 'True', 'ret == (a >> b)',"
                   "lambda a, b: b if a else True)")

        self.assertProgramSafe(program)

        program = ("ex_imp = define_('bool -> bool -> bool', 'True', 'ret = (a >> b)',"
                   "lambda a, b: b if a else True)")

        with self.assertRaises(ParseException):
            self.assertProgramSafe(program)

    @unittest.skip
    def test_outer_lambda_call(self):
        example1 = """example1 = define_('int -> int -> int', 'a >= b', 'ret >= 0',
                          lambda a, b: a - b)"""
        program = _unlines(example1,
                           """example_lam_outer = define_('int -> int', 'a > 1', 'ret >= 1',
                              lambda a: example1(a, 1) + 1)""")

        self.assertProgramSafe(program)

        program = _unlines(example1,
                           """example_lam_outer = define_('int -> int', 'a > 1', 'ret >= 1',
                              lambda a: example1(a, 1))""")

        self.assertProgramUnSafe(program)

        program = _unlines(example1,
                           """example_lam_outer = define_('int -> int', 'a > 1', 'ret >= 1',
                              lambda a: example1(a, 3))""")

        self.assertProgramUnSafe(program)

    def assertProgramSafe(self, program):
        counterexample = check_program(program)
        self.assertIsNone(counterexample)

    def assertProgramUnSafe(self, program):
        counterexample = check_program(program)
        self.assertIsNotNone(counterexample)


if __name__ == '__main__':
    unittest.main()
