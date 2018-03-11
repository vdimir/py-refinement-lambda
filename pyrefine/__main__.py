#!/usr/bin/env python
"""Run check specified file."""

import sys
import ast

from .ast_parser import get_invocations_model, get_lambdas_model
from .checker import check_lambda_model, check_invocation_model
from operator import attrgetter


def main():
    """Script entry point."""
    fname = sys.argv[1]
    with open(fname) as f:
        s = f.read()

    program_ast = ast.parse(s, fname)

    lambda_models = get_lambdas_model(program_ast)
    lambda_models = dict(map(lambda m: (m.func_name, m), lambda_models))
    for lam_model in lambda_models.values():
        is_sat = check_lambda_model(lam_model)
        if is_sat:
            print(lam_model.func_name)
            print(is_sat)
            assert not is_sat
    invocations = get_invocations_model(program_ast, lambda_models)

    for m in invocations:
        print(m[0])
        res = check_invocation_model(m[1], lambda_models)
        print("SAFE." if res is None else "UNSAFE!")
        print()
        # if res is not None:
        #     print("UNSAFE!")
        #     print("Wrong function at line: {}\nCounterexample: {}."
        #           .format(m.src_data['lineno'], res))
        # else:
        #     print('SAFE.')
        # print()


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
