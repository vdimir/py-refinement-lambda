#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from pyrefine.checker import check_program


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)

    defined_funcs = check_program(program_ast, raise_exception=False)
    for n, e in defined_funcs.items():
        if e is None:
            print(n, "ok.")
        else:
            print(n, "Error: ", str(e))


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)
    try:
        main()
    except Exception as e:
        print()
        print("Exception:")
        print(e)
