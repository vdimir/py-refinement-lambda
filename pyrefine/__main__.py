#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from pyrefine.checker import check_program
from sty import fg, ef, rs


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    print_counterexample = '--print-counterexample' in sys.argv
    program_ast = ast.parse(s, fname)

    defined_funcs = check_program(program_ast, raise_exception=False)
    for n, e in defined_funcs.items():
        if e.is_ok():
            print("Checking {name_format}{name}{rs}... {color}Ok.{rs}".format(
                name=n, color=fg.green, rs=rs.all, name_format=ef.bold))
            for c in e.child:
                print("  {} - {color}Ok.{rs}".format(c, rs=rs.all, color=fg.green))

        else:
            print("Checking {name_format}{name}{rs}... {color}Error:{rs}\n\t"
                  "{err}{rs}".format(name=n, err=str(e.err), color=fg.red,
                                     rs=rs.all, name_format=ef.bold))
            if print_counterexample:
                print("Counterexample:")
                print(e.err.counterexample)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)
    main()
