#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from pyrefine.checker.check_program import check_program


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)
    res = check_program(program_ast)
    print(res)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
