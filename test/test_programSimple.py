import unittest

from pyrefine.checker import check_program

from pyrefine.exceptions import *


program_simple = r"""
def main():
    define_('int', 'True', 'ret == 0')

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


    example_diff_sign = define_('int -> int -> int',
                                'a*b < 0',
                                'ret > 0',
                                lambda a, b: a if a > b else b)

    x = example_simple2(5, 7)
    z = c_('int', 5)
    x = example_simple2(example_simple1(2), 1)
    x = example_simple2(example_simple1(z), z)
    x = 0
    return x

if __name__ == '__main__':
    main()
    print('Done')

"""


class TestProgramSimple(unittest.TestCase):
    def test_simple(self):
        res = check_program(program_simple)
        self.assertIn('main', res)
