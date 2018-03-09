#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from .ast_parser.lambda_parser import get_lambdas_model
from .checker import check_lambda_model


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)

    models = get_lambdas_model(program_ast)
    for m in models:
        print(m)
        res = check_lambda_model(m)
        if res is not None:
            print("UNSAFE!")
            print("Wrong function at line: {}\nCounterexample: {}."
                  .format(m.src_data['lineno'], res))
        else:
            print('SAFE.')
        print()


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
