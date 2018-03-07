#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from .checker import check_all_lambdas


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)
    check_all_lambdas(program_ast)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
