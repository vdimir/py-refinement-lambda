import ast
import z3
from pyrefine.model.vars_context import ScopedContext

from pyrefine.checker.invocation_model import process_invocation_model
from pyrefine.model.types import ModelVar

from pyrefine.checker.check_lambda import check_lambda, get_checked_lambda_definitions

from pyrefine.checker.common import expr_to_z3
from pyrefine.helpers import UniquePrefix
from pyrefine.ast_parser import get_assign_expr_model
from pyrefine.exceptions import WhileDefinitionException, LambdaDefinitionException, \
    CheckerException
from pyrefine.model import ExpressionModel, VarsContext, LambdaModel, InvocationModel
from pyrefine.ast_parser.funcdef_parser import NameVisitor, parse_loop_definition, \
    AssignNameVisitor
from pyrefine.z3_wrapper import proof


class FuncDefCheckVisitor(ast.NodeVisitor):
    def __init__(self, defined_funcs=None):
        self.var_scope = None
        self.constraints = []
        self.defined_funcs = ScopedContext(parent=ScopedContext(values=defined_funcs))
        self.ret_vals = []

    def visit_If(self, node):
        cond_names = NameVisitor.get_names(node.test)
        cond_ast = ExpressionModel(node.test)

        cur_scope = self.var_scope
        cond_expr, _ = expr_to_z3(cond_ast,
                                  cur_scope)

        if_true_scope = VarsContext(parent_ctx=cur_scope)
        if_false_scope = VarsContext(parent_ctx=cur_scope)
        idfun = lambda x: x

        for name in cond_names:
            if_true_scope.update(name)
            if_false_scope.update(name)
            self.constraints.append(cur_scope[name] == z3.If(cond_expr, if_true_scope[name], if_false_scope[name]))

        for branch_scope, neg_opt, body in zip([if_true_scope, if_false_scope],
                                               [idfun, z3.Not],
                                               [node.body, node.orelse]):
            branch_cond_expr = expr_to_z3(cond_ast, branch_scope, self.constraints)
            self.constraints.append(neg_opt(branch_cond_expr))

            self.var_scope = branch_scope
            self.visit_list(body)
            self.var_scope = cur_scope

        name_to_update = list()
        name_to_update += list(if_true_scope.variables.values.keys())
        name_to_update += list(if_false_scope.variables.values.keys())

        for name in set(name_to_update):
            new_var = self.var_scope.later_update(name)
            self.constraints.append(new_var == z3.If(cond_expr, if_true_scope[name], if_false_scope[name]))
            self.var_scope.later_update_finish(name, new_var)

    def visit_list(self, statement_list):
        for stmt in statement_list:
            self.visit(stmt)

    def visit_While(self, node):
        loop_def, *body = node.body

        loop_inv, dec_func = parse_loop_definition(loop_def)

        cond_names = NameVisitor.get_names(node.test)
        updated_var_names = AssignNameVisitor.get_names(node)
        cond_names += updated_var_names
        cond_names = set(cond_names)

        cond_ast = ExpressionModel(node.test)

        def check_invariant(scope):
            inv_exp = expr_to_z3(loop_inv, scope, self.constraints)
            counterexample = proof(self.constraints, inv_exp)
            if counterexample:
                raise WhileDefinitionException(reason="Invariant not hold",
                                               counterexample=counterexample,
                                               src_info={'lineno': node.lineno})
            return inv_exp

        cur_scope = self.var_scope
        check_invariant(cur_scope)

        while_inner_scope = VarsContext(parent_ctx=cur_scope)

        for name in cond_names:
            while_inner_scope.update(name)

        self.var_scope = while_inner_scope
        inv_pre_exp = expr_to_z3(loop_inv, while_inner_scope, self.constraints,
                                 defined_funcs=self.defined_funcs)
        dec_func_before = expr_to_z3(dec_func, while_inner_scope, self.constraints,
                                     defined_funcs=self.defined_funcs)

        self.constraints.append(inv_pre_exp)
        test_cond = expr_to_z3(cond_ast, while_inner_scope, self.constraints,
                               defined_funcs=self.defined_funcs)
        self.constraints.append(test_cond)

        self.visit_list(body)
        check_invariant(while_inner_scope)

        dec_func_after = expr_to_z3(dec_func, while_inner_scope, self.constraints,
                                    defined_funcs=self.defined_funcs)

        def assert_while(counterexample, msg):
            raise WhileDefinitionException(reason=msg, counterexample=counterexample,
                src_info={'lineno': node.lineno})

        opt = z3.Optimize()
        for c in self.constraints:
            if isinstance(c, bool):
                continue
            opt.add(c)

        h = opt.minimize(dec_func_after)
        res = opt.check()
        if res != z3.sat:
            assert_while(None, "Loop function cant be minimized!")

        model = opt.model()
        dec_min = model.evaluate(dec_func_after)
        test_cond_after = expr_to_z3(cond_ast, while_inner_scope, self.constraints,
                                     defined_funcs=self.defined_funcs)
        break_on_zero = z3.Implies(dec_func_after == dec_min, z3.Not(test_cond_after))
        counterexample = proof(self.constraints, break_on_zero)

        if counterexample:
            assert_while(counterexample,
                         "Loop function equals zero not follow end of loop!")

        counterexample = proof(self.constraints, z3.Not(dec_func_after == dec_min))
        if counterexample is None:
            assert_while(counterexample, "Loop function not reach minimum!")

        counterexample = proof(self.constraints, dec_func_before > dec_func_after)
        if counterexample:
            assert_while(counterexample, "Loop function not decrease!")

        counterexample = proof(self.constraints, dec_func_after >= 0)
        if counterexample:
            assert_while(counterexample, "Loop function not positive!")

        self.var_scope = cur_scope

        name_to_update = set(while_inner_scope.variables.values.keys())

        for name in set(name_to_update):
            self.var_scope.update(name)

        test_cond = expr_to_z3(cond_ast, self.var_scope, self.constraints)
        inv_post_expr = expr_to_z3(loop_inv, self.var_scope, self.constraints)
        self.constraints.append(z3.Not(test_cond))
        self.constraints.append(inv_post_expr)

    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_Assign(self, node: ast.Assign):
        assigns = get_assign_expr_model(node, self.defined_funcs, strict=True)

        assigns = list(map(lambda a: (a[0], a[1], self.eval_expr(a[2])), assigns))
        for i, (target_name, var_type, value) in enumerate(assigns):
            if var_type is None:
                self.var_scope.update(target_name)
                self.constraints.append(self.var_scope[target_name] == value)
                continue

            if isinstance(var_type, ModelVar):
                if target_name in self.var_scope.functions:
                    raise CheckerException(
                        reason='Function `{}` already defined.'.format(target_name))
                if target_name in self.var_scope:
                    defined_type = self.var_scope.get_var_type(target_name)
                    if type(defined_type) == type(var_type):
                        self.var_scope.update(target_name)
                        self.constraints.append(self.var_scope[target_name] == value)
                        continue
                    else:
                        raise CheckerException(
                            reason='Variable `{}` already of type {} defined.'
                            .format(target_name, defined_type))
                self.var_scope.add_var(target_name, var_type)
                self.constraints.append(self.var_scope[target_name] == value)
                continue

            if var_type == 'FUNCTION':
                if target_name in self.var_scope.variables:
                    raise CheckerException(
                        reason='Variable `{}` already defined.'.format(target_name))
                assert isinstance(value, LambdaModel)
                self.defined_funcs[target_name] = value
                continue
            raise Exception("Unreachable code!")

    def visit_Assert(self, node):
        test = ExpressionModel(node.test)
        assert_expr = expr_to_z3(test, self.var_scope, self.constraints, defined_funcs=self.defined_funcs)
        counterexample = proof(self.constraints, assert_expr )

        if counterexample:
            raise CheckerException(src_info={'lineno': node.lineno},
                                   counterexample=counterexample,
                                   reason="Assert not hold!")

    def visit_Return(self, node):
        value = expr_to_z3(ExpressionModel(node.value), self.var_scope, self.constraints)
        self.ret_vals.append(value)

    def visit(self, node):
        super().visit(node)

    def eval_expr(self, exp):
        if isinstance(exp, ExpressionModel):
            return expr_to_z3(exp, self.var_scope, self.constraints,
                              defined_funcs=self.defined_funcs)
        if isinstance(exp, LambdaModel):
            check_lambda(exp, self.var_scope, self.defined_funcs, self.constraints)
            return exp
        if isinstance(exp, InvocationModel):
            res = process_invocation_model(exp, self.defined_funcs,
                                           self.var_scope, self.constraints)
            new_const, ret_var = res
            self.constraints += new_const
            return ret_var

        raise Exception("Unreachable code!")

    def visit_Expr(self, node):
        if isinstance(node.value, ast.Call) and node.value.func.id == 'print':
            return
        self.generic_visit(node)

    def generic_visit(self, node):
        raise Exception("{} not allowed".format(type(node)))


def check_global_scope(program):
    return get_checked_lambda_definitions(program)


def check_func_model(func_model, defined_funcs=None):
    visitor = FuncDefCheckVisitor(defined_funcs=defined_funcs)
    func_var_cxt = VarsContext(name_map=UniquePrefix(custom_prefix=func_model.func_name),
                               variables=func_model.args)
    for func_name, other_func_model in defined_funcs.items():
        func_var_cxt.functions.add(other_func_model.func_name,
                                   other_func_model.args['ret'])

    visitor.var_scope = func_var_cxt
    constraints = []
    pre_z3_cond = expr_to_z3(func_model.pre_cond, func_var_cxt, constraints, dsl=True)

    post_z3_cond, _ = expr_to_z3(func_model.post_cond, func_var_cxt, dsl=True)

    visitor.constraints.append(pre_z3_cond)
    for stmt in func_model.body:
        visitor.visit(stmt)

    for ret_val in visitor.ret_vals:
        ret_var_bind = func_var_cxt['ret'] == ret_val

        counterexample = proof(visitor.constraints+[ret_var_bind], post_z3_cond)
        if counterexample:
            raise LambdaDefinitionException(func_model.src_data, func_model.func_name,
                                            counterexample)
    return visitor.defined_funcs


