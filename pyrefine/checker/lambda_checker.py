import z3

from pyrefine.ast_parser import get_lambdas_model
from pyrefine.exceptions import LambdaDefinitionException
from pyrefine.model import LambdaModel
from pyrefine.ast_parser.expr_parser import expr_model_to_z3


def check_lambda_model(lambda_model: LambdaModel):
    solver = z3.Solver()
    var_ctx = lambda_model.variables.as_z3_ctx()

    pre_z3_cond = expr_model_to_z3(lambda_model.pre_cond, var_ctx, dsl=True)
    post_z3_cond = expr_model_to_z3(lambda_model.post_cond, var_ctx, dsl=True)
    solver.add(pre_z3_cond)

    ret_var = var_ctx.get_z3_var_list()[-1]
    ret_var_bind = ret_var == expr_model_to_z3(lambda_model.body, var_ctx, dsl=False)

    solver.add(ret_var_bind)
    solver.add(z3.Not(post_z3_cond))
    check = solver.check()

    if check == z3.unsat:
        return
    return solver.model()


def check_all_lambdas(program_ast):
    models = get_lambdas_model(program_ast)
    for m in models:
        res = check_lambda_model(m)
        if res is not None:
            raise LambdaDefinitionException(m.src_data, m.func_name)
    return models
