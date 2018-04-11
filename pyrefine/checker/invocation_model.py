from typing import Dict
from pyrefine.exceptions import ErrorCallException
from pyrefine.helpers import UniquePrefix
from pyrefine.ast_parser.expr_parser import expr_model_to_z3
from pyrefine.model import InvocationModel, LambdaModel, VarsContext
import z3


def process_invocation_model(model, lambda_models, global_ctx, global_constraints):
    assert isinstance(model, InvocationModel)
    counterexample = check_invocation_model(model, lambda_models,
                                            global_ctx, global_constraints)

    assert counterexample is None
    result = invocation_model_assertions(model, lambda_models,
                                         global_ctx, global_constraints)
    constraints, _, ret_var = result

    return constraints, ret_var


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
