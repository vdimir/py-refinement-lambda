import unittest

from pyrefine.checker import check_program

from pyrefine.exceptions import *


def _unlines(*lines):
    return "\n".join(lines)


def _wrap_code_in_func(*lines, func_name='foo'):
    return ''.join(["def {}():\n\t".format(func_name),
                    "define_('int', 'True', 'ret == 0')\n\t",
                    "\n\t".join(lines),
                    "\n\treturn 0\n"
                    ])


class TestFunctionDef(unittest.TestCase):

    def test_redefine(self):

        with self.assertRaises(CheckerException) as e:
            check_program(_wrap_code_in_func(
                "x = c_('int', 5)",
                "x = c_('bool', True)"))
        self.assertEqual(e.exception.reason, "Variable `x` already of type Int defined.")

        with self.assertRaises(CheckerException) as e:
            check_program(_wrap_code_in_func(
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)",
                "x = define_('int -> int', 'True', 'True', lambda x: x + 6)"))
        self.assertEqual(e.exception.reason, "Variable `x` already defined.")

        with self.assertRaises(CheckerException) as e:
            check_program(_wrap_code_in_func(
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)",
                "x = c_('int', 5)"))
        self.assertEqual(e.exception.reason, "Function `x` already defined.")

        with self.assertRaises(VariableNotFoundException) as e:
            check_program(_wrap_code_in_func(
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)",
                "x = 5"))
        self.assertEqual(e.exception.var_name, "x")

        with self.assertRaises(CheckerException) as e:
            check_program(_wrap_code_in_func(
                "x = c_('int', 5)",
                "x = define_('int -> int', 'True', 'True', lambda x: x + 5)"))
        self.assertEqual(e.exception.reason, "Variable `x` already defined.")

    def test_namehiding(self):
        program = _wrap_code_in_func(
            "x = c_('int', -5)",
            "f = define_('int -> int', 'x > 0', 'ret > 1',"
                "lambda x: x + 1)",
            "f2 = define_('int -> int', 'a > 0', 'ret == -5',"
                "lambda a: x)",
            func_name='foo'
        )
        res = check_program(program)
        self.assertIn('foo', res)

    def test_globalFuncInCond(self):
        program = _wrap_code_in_func(
            "f = define_('int', 'True', 'ret < 0',  lambda: -5)",
            "g = define_('int -> int', 'x > -f()', 'ret > 1', lambda x: x + 1)",
            func_name='foo')
        res = check_program(program)
        self.assertIn('foo', res)

        program = _wrap_code_in_func(
            "abs_ = define_('int -> int', 'True', "
                "'(x >= 0) >> (ret == x) and (x < 0) >> (ret == -x)',"
                "lambda x: x if x > 0 else -x)",
            "g = define_('int -> int', 'True', 'ret > abs_(x)',lambda x: x*x + 1)",
            func_name='foo')
        res = check_program(program)
        self.assertIn('foo', res)

