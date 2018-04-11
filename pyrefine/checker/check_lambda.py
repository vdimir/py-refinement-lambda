import z3

from pyrefine.ast_parser import get_lambdas_model
from pyrefine.ast_parser.expr_parser import expr_model_to_z3
from pyrefine.checker.common import process_substitutions

from pyrefine.model import VarsContext

from pyrefine.helpers import UniquePrefix, merge_dict

from pyrefine.exceptions import LambdaDefinitionException
from collections import OrderedDict as odict


def get_checked_lambda_definitions(program, global_ctx=None,
                                   lambda_models=None,
                                   global_constraints=None):
    if global_ctx is None:
        global_ctx = VarsContext()
    if lambda_models is None:
        lambda_models = odict()
    if global_constraints is None:
        global_constraints = []

    new_lambda_models = get_lambdas_model(program)

    for lambda_model in new_lambda_models.values():
        check_lambda(lambda_model, global_ctx, lambda_models, global_constraints)

    merge_dict(lambda_models, new_lambda_models)
    return global_ctx, lambda_models


def check_lambda(lambda_model, global_ctx=None,
                 lambda_models_dict=None, global_constraints=None):
    if lambda_models_dict is None:
        lambda_models_dict = odict()

    name_map = UniquePrefix(custom_prefix=lambda_model.func_name)
    var_ctx = VarsContext(variables=lambda_model.args,
                          name_map=name_map,
                          parent_ctx=global_ctx)

    subst_constraints = []
    pre_z3_cond, subst = expr_model_to_z3(lambda_model.pre_cond, var_ctx, dsl=True)

    subst_constraints += process_substitutions(subst, lambda_models_dict, var_ctx,
                                               global_constraints=[pre_z3_cond])

    post_z3_cond, subst = expr_model_to_z3(lambda_model.post_cond, var_ctx, dsl=True)

    subst_constraints += process_substitutions(subst, lambda_models_dict, var_ctx,
                                               global_constraints=[pre_z3_cond])

    var_ctx = VarsContext(variables=lambda_model.args,
                          name_map=name_map,
                          parent_ctx=global_ctx)

    body_z3, subst = expr_model_to_z3(lambda_model.body, var_ctx, dsl=False)

    subst_constraints += process_substitutions(subst, lambda_models_dict, var_ctx,
                                               global_constraints=[pre_z3_cond])

    ret_var_bind = var_ctx.get_var_z3('ret') == body_z3

    if global_ctx is not None:
        global_ctx.functions.add(lambda_model.func_name,
                                 lambda_model.args['ret'])

    solver = z3.Solver()

    solver.add(pre_z3_cond)
    solver.add(*subst_constraints)
    if global_constraints is not None:
        solver.add(*global_constraints)

    solver.add(ret_var_bind)
    solver.add(z3.Not(post_z3_cond))

    check = solver.check()
    if check != z3.unsat:
        model = None
        if check == z3.sat:
            model = solver.model()
        raise LambdaDefinitionException(lambda_model.src_data, lambda_model.func_name,
                                        model)
