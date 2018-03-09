import ast
import unittest

from pyrefine.checker import check_lambda_model

from pyrefine.ast_parser.lambda_parser import get_lambdas_model

program_simple = r"""
def main():
    example_simple1 = define_('int -> int', 'a > 0', 'ret > 1',
                               lambda a: 2 if a == 1 else a * 2)

    example_simple2 = define_('int -> int -> int',
                              'a >= 0 and b >= 0',
                              'ret >= 0 and (ret <= a or ret <= b)',
                              lambda a, b: (a + b) // 2)

    example_chain_comp = define_('int -> bool',
                                  '1 <= x <= 2',
                                  'ret == True',
                                  lambda x: 2 <= x*2 <= 4)

    example_simple_wrong = define_('int -> int -> int',
                                  'x > 0 and y > 0',
                                  'ret > 1',
                                  lambda x, y : x*y)

    x = example_simple2(5, 7)
    x = example_simple2(example_simple1(2), 1)
    z = 10
    x = example_simple2(example_simple1(z), z)

if __name__ == '__main__':
    main()
    print('Done')

"""


class TestLambdaChecker(unittest.TestCase):

    def test_lambda_simple(self):
        program_ast = ast.parse(program_simple, "main.py")

        models = get_lambdas_model(program_ast)

        models = dict(map(lambda m: (m.func_name, m), models))

        all_names = ['example_simple1', 'example_simple2',
                     'example_chain_comp', 'example_simple_wrong']
        self.assertSetEqual(set(all_names), set(models.keys()))

        for n in ['example_simple1', 'example_simple2', 'example_chain_comp']:
            self.assertIsNone(check_lambda_model(models[n]))

        res = check_lambda_model(models['example_simple_wrong'])
        self.assertIsNotNone(res)

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

    def assertProgramSafe(self, program):
        program_ast = ast.parse(program, "main.py")
        models = get_lambdas_model(program_ast)
        for model in models:
            res = check_lambda_model(model)
            self.assertIsNone(res)

    def assertProgramUnSafe(self, program):
        program_ast = ast.parse(program, "main.py")
        models = get_lambdas_model(program_ast)
        for model in models:
            res = check_lambda_model(model)
            if res is not None:
                return
        self.fail("No one unsafe!")


if __name__ == '__main__':
    unittest.main()
