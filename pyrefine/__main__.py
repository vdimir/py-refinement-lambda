#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from .ast_parser.lambda_parser import get_lambdas_model
from .checker import check_all_lambdas, check_lambda_model


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)

    models = get_lambdas_model(program_ast)
    for m in models:
        print(m)
        check_lambda_model(m)
        print()


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
