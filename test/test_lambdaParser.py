import unittest

from pyrefine.ast_parser.lambda_parser import parse_type_def_str

from pyrefine.model import types as model_types


class TestLambdaParser(unittest.TestCase):
    def test_parse_type_def_simple(self):

        func_type = parse_type_def_str('int -> bool -> int')
        self.assertIsInstance(func_type[0], model_types.IntVar)
        self.assertIsInstance(func_type[1], model_types.BoolVar)
        self.assertIsInstance(func_type[2], model_types.IntVar)
        self.assertEqual(len(func_type), 3)

    def test_parse_type_def_func1(self):

        func_type = parse_type_def_str('int -> (int -> int) -> int')
        self.assertIsInstance(func_type[0], model_types.IntVar)
        self.assertIsInstance(func_type[1], model_types.FuncVar)
        self.assertEqual(len(func_type[1].arg_types), 2)
        self.assertIsInstance(func_type[1].arg_types[0], model_types.IntVar)
        self.assertIsInstance(func_type[1].arg_types[1], model_types.IntVar)
        self.assertIsInstance(func_type[2], model_types.IntVar)

    def test_parse_type_def_func2(self):

        func_type = parse_type_def_str('(int -> int -> bool) -> bool -> int')
        self.assertIsInstance(func_type[0], model_types.FuncVar)
        self.assertEqual(len(func_type[0].arg_types), 3)


if __name__ == '__main__':
    unittest.main()
