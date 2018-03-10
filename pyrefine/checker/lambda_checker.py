import z3

from ..ast_parser.lambda_parser import get_lambdas_model


def check_lambda_model(lambda_model):
    solver = z3.Solver()
    solver.add(lambda_model.pre_cond)

    ret_var_name = lambda_model.ret_var_name
    ret_var_bind = lambda_model.variables.get_var_z3(ret_var_name) == lambda_model.body

    solver.add(ret_var_bind)
    solver.add(z3.Not(lambda_model.post_cond))
    check = solver.check()

    if check == z3.unsat:
        return
    return solver.model()


# def check_all_lambdas(program_ast):
#     models = get_lambdas_model(program_ast)
#     for m in models:
#         check_lambda_model(m)
