import ast

from collections import OrderedDict as odict

from pyrefine.ast_parser import get_assign_expr_model
from pyrefine.ast_parser.expr_list_parser import get_expr_to_check
from pyrefine.exceptions import ErrorCallException, LambdaDefinitionException

from pyrefine.ast_parser.expr_parser import expr_model_to_z3
from pyrefine.helpers import UniquePrefix, merge_dict
from pyrefine.model import VarsContext, InvocationModel, LambdaModel, ExpressionModel
from ..ast_parser import get_lambdas_model
from typing import Dict

import z3


def check_program(program):
    if isinstance(program, str):
        program = ast.parse(program)
    scopes = get_expr_to_check(program)

    global_ctx = VarsContext()
    lambda_models = odict()
    global_constraints = []

    check_expr_list(scopes['_module'], global_ctx, lambda_models, global_constraints)

    for scope_name, expr_list in scopes.items():
        if scope_name == '_module':
            continue

        scope_global_ctx = VarsContext(parent_ctx=global_ctx)
        scope_lambda_models = lambda_models.copy()
        scope_global_constraints = global_constraints.copy()
        check_expr_list(expr_list,
                        scope_global_ctx,
                        scope_lambda_models,
                        scope_global_constraints)


def check_expr_list(expr_list, global_ctx, lambda_models, global_constraints):
    for expr in expr_list:
        check_generic_expr(expr, global_ctx, lambda_models, global_constraints)


def check_generic_expr(program, global_ctx, lambda_models, global_constraints):
    get_checked_lambda_definitions(program, global_ctx, lambda_models, global_constraints)

    top_level_assign = get_assign_expr_model(program, defined_functions=lambda_models)

    for target_name, ret_type, var_value in top_level_assign:
        constraints, ret_var = check_model(var_value, lambda_models,
                                           global_ctx, global_constraints)

        global_constraints += constraints
        global_ctx.add_var(target_name, ret_type)
        global_constraints.append(ret_var == global_ctx.get_var_z3(target_name))

    return global_ctx, lambda_models, global_constraints


def check_model(model, lambda_models, global_ctx, global_constraints):
    if isinstance(model, InvocationModel):
        counterexample = check_invocation_model(model, lambda_models,
                                                global_ctx, global_constraints)

        assert counterexample is None
        result = invocation_model_assertions(model, lambda_models,
                                             global_ctx, global_constraints)
        constraints, _, ret_var = result

    elif isinstance(model, ExpressionModel):
        ret_var, subst = expr_model_to_z3(model, global_ctx, dsl=False)

        constraints = process_substitutions(subst, lambda_models, global_ctx,
                                            global_constraints=global_constraints)
    elif isinstance(model, LambdaModel):
        check_lambda(model, global_ctx, lambda_models, global_constraints)
        constraints = []
        ret_var = None
    else:
        raise Exception("Unreachable code.")

    return constraints, ret_var


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
        check_model(lambda_model, lambda_models, global_ctx, global_constraints)

    merge_dict(lambda_models, new_lambda_models)
    return global_ctx, lambda_models


def check_lambda(lambda_model, global_ctx=None,
                 lambda_models_dict=None, global_constraints=None):
    if lambda_models_dict is None:
        lambda_models_dict = odict()

    name_map = UniquePrefix(custom_prefix=lambda_model.func_name)
    var_ctx = VarsContext(variables=lambda_model.args,
                          name_map=name_map)

    pre_z3_cond, _ = expr_model_to_z3(lambda_model.pre_cond, var_ctx, dsl=True)
    post_z3_cond, _ = expr_model_to_z3(lambda_model.post_cond, var_ctx, dsl=True)

    var_ctx = VarsContext(variables=lambda_model.args,
                          name_map=name_map,
                          parent_ctx=global_ctx)

    body_z3, subst = expr_model_to_z3(lambda_model.body, var_ctx, dsl=False)

    subst_constraints = process_substitutions(subst, lambda_models_dict, var_ctx,
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
        raise LambdaDefinitionException(lambda_model.src_data, lambda_model.func_name)


def invocation_model_assertions(invocation_model: InvocationModel,
                                lambda_models: Dict[str, LambdaModel],
                                var_cxt, global_constraints):
    lambda_model = lambda_models[invocation_model.func_name]
    assert invocation_model.func_name == lambda_model.func_name
    constraints = []
    prefix_gen = UniquePrefix(custom_prefix=invocation_model.func_name + "$call")

    local_context = VarsContext(variables=lambda_model.args,
                                name_map=prefix_gen,
                                parent_ctx=var_cxt)

    *arg_names, ret_var_name = list(lambda_model.args.keys())
    for local_var_name, local_var_val in zip(arg_names, invocation_model.args):
        arg_model, new_subst = expr_model_to_z3(local_var_val, var_cxt, False)

        new_constraints = process_substitutions(new_subst, lambda_models, var_cxt,
                                                global_constraints)
        constraints += new_constraints
        constraints.append(arg_model == local_context.get_var_z3(local_var_name))

    post_cond, _ = expr_model_to_z3(lambda_model.post_cond, local_context, dsl=True)
    constraints.append(post_cond)
    return constraints, local_context, local_context.get_var_z3(ret_var_name)


def process_substitutions(substitutions, lambda_models, var_cxt, global_constraints):
    constraints = []
    for (substituted, var_in_outer_scope) in substitutions.values():
        result = invocation_model_assertions(substituted, lambda_models, var_cxt, global_constraints)
        new_constraints, new_local_context, new_ret_var = result

        is_sat = check_invocation_model(substituted, lambda_models, var_cxt, global_constraints)
        if is_sat:
            print(is_sat)
            raise ErrorCallException(substituted.src_data,
                                     substituted.func_name)
        constraints += new_constraints
        constraints.append(new_ret_var == var_in_outer_scope)

    return constraints


def check_invocation_model(invocation_model: InvocationModel,
                           lambda_models: Dict[str, LambdaModel],
                           var_cxt,
                           global_constraints):

    result = invocation_model_assertions(invocation_model, lambda_models,
                                         var_cxt, global_constraints)
    constraints, local_context, ret_var = result

    lambda_model = lambda_models[invocation_model.func_name]
    expected_arg_num = len(lambda_model.args) - 1
    actual_arg_num = len(invocation_model.args)
    if expected_arg_num != actual_arg_num:
        raise ErrorCallException(src_info=invocation_model.src_data,
                                 name=invocation_model.func_name,
                                 reason="Wrong number of arguments (expected: "
                                        "{}, actual: {}".format(expected_arg_num,
                                                                actual_arg_num))
    pre_cond, _ = expr_model_to_z3(lambda_model.pre_cond, local_context, dsl=True)

    s = z3.Solver()
    s.add(*constraints)

    if global_constraints is not None:
        s.add(*global_constraints)

    s.add(z3.Not(pre_cond))
    check = s.check()
    if check != z3.unsat:
        raise ErrorCallException(name=invocation_model.func_name,
                                 src_info=invocation_model.src_data)
