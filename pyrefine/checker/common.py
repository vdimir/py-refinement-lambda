from pyrefine.checker.invocation_model import process_substitutions

from pyrefine.ast_parser.expr_parser import expr_model_to_z3


def expr_to_z3(expr, var_ctx, constraints=None, dsl=False, defined_funcs=None):
    if defined_funcs is None:
        defined_funcs = {}

    ret_var, subst = expr_model_to_z3(expr, var_ctx, dsl=dsl)

    new_constraints = process_substitutions(subst, defined_funcs, var_ctx,
                                            global_constraints=constraints)
    if constraints is None:
        return ret_var, constraints

    constraints += new_constraints
    return ret_var

