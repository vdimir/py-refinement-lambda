import z3

from pyrefine.exceptions import CheckerException, ErrorCallException

from pyrefine.ast_parser.expr_parser import ReplaceCallExprVisitor, expr_model_to_z3
from pyrefine.helpers import UniquePrefix

from pyrefine.model import VarsContext, LambdaModel, InvocationModel, VarsZ3Context, \
    ExpressionModel
from typing import Dict


def invocation_model_assertions(invocation_model: InvocationModel,
                                lambda_models: Dict[str, LambdaModel],
                                global_var_cxt: VarsZ3Context,
                                ret_var_types):
    lambda_model = lambda_models[invocation_model.func_name]
    assert invocation_model.func_name == lambda_model.func_name
    res = []

    prefix_gen = UniquePrefix()
    local_context = lambda_model.variables.as_z3_ctx(prefix_gen)
    *local_lambda_vars, ret_var = local_context.get_z3_var_list()

    for local_var_name, local_var_val in zip(local_lambda_vars, invocation_model.args):
        arg_model, subst = expr_model_to_z3_invokation(local_var_val, global_var_cxt,
                                                       False, ret_var_types)
        for (substituted_inv, var_in_outer_scope) in subst.values():
            constraints, new_local_context = invocation_model_assertions(substituted_inv,
                                                                         lambda_models,
                                                                         global_var_cxt,
                                                                         ret_var_types)

            is_sat = check_invocation_model(substituted_inv, lambda_models)
            if is_sat:
                raise ErrorCallException(substituted_inv.src_data,
                                         substituted_inv.func_name)

            new_ret_var = new_local_context.get_z3_var_list()[-1]
            constraints.append(new_ret_var == var_in_outer_scope)
            res += constraints
        res.append(arg_model == local_var_name)

    post_cond = expr_model_to_z3(lambda_model.post_cond, local_context, dsl=True)
    res.append(post_cond)

    return res, local_context


def expr_model_to_z3_invokation(expr_model: ExpressionModel,
                     var_ctx: VarsZ3Context,
                     dsl: bool,
                     ret_var_types):
    expr_visitor = ReplaceCallExprVisitor(var_ctx, dsl=dsl)
    expr_visitor.func_ret_types = ret_var_types
    expr_visitor.visit(expr_model.expr_ast)
    return expr_visitor.pop_result(), expr_visitor.substitutions


def get_simple_lambdas_ctx(lambda_models: Dict[str, LambdaModel]):
    ret_var_types = {}

    global_var_ctx = VarsContext()
    for name, func in lambda_models.items():
        ret_var_types[func.func_name] = list(func.variables.variables.values())[-1]
        f_var, is_simple = func.as_simple_func()
        if not is_simple:
            continue
        global_var_ctx.add_var(name, f_var)
    return global_var_ctx, ret_var_types


def check_invocation_model(invocation_model: InvocationModel,
                           lambda_models: Dict[str, LambdaModel]):

    global_var_ctx, ret_var_types = get_simple_lambdas_ctx(lambda_models)
    global_var_ctx_z3 = global_var_ctx.as_z3_ctx()

    try:
        constraints, local_context = invocation_model_assertions(invocation_model, lambda_models,
                                                       global_var_ctx_z3, ret_var_types)
    except CheckerException as e:
        return True

    lambda_model = lambda_models[invocation_model.func_name]
    local_context.parent_context = global_var_ctx_z3
    pre_cond = expr_model_to_z3(lambda_model.pre_cond, local_context, dsl=True)

    s = z3.Solver()
    s.add(*constraints)
    s.add(z3.Not(pre_cond))

    # print(s.assertions())
    is_sat = s.check() == z3.sat
    if is_sat:
        return s.model()
