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
        assert not is_sat
    invocations = get_invocations_model(program_ast, lambda_models)

    for m in invocations:
        is_sat = check_invocation_model(m[1], lambda_models)
        assert not is_sat


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: %s <file.py>" % sys.argv[0])
        sys.exit(0)

    main()
