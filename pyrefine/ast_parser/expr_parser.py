import ast
import uuid
from collections import deque

from pyrefine.helpers import UniquePrefix

from pyrefine.exceptions import ParseException
from pyrefine.model import InvocationModel
from .mapping import operator_ast_to_model
from ..model import operators
from ..model import ExpressionModel, VarsContext


def str_to_ast(expr_str: str) -> ExpressionModel:
    exp = ast.parse(expr_str)
    expr_ast = exp.body

    if not (len(expr_ast) == 1 and isinstance(expr_ast[0], ast.Expr)):
        raise ParseException(expr_str)

    expr_ast = expr_ast[0].value
    return ExpressionModel(expr_ast)


def expr_model_to_z3(expr_model: ExpressionModel,
                     var_ctx: VarsContext,
                     dsl: bool):
    expr_visitor = ExprVisitor(var_ctx, dsl=dsl)
    expr_visitor.visit(expr_model.expr_ast)
    return expr_visitor.pop_result(), expr_visitor.substitutions


class ExprVisitor(ast.NodeVisitor):
    def __init__(self, var_ctx, dsl=False):
        self.dsl_enabled = dsl
        self.res = deque()
        self.var_ctx = var_ctx
        self.substitutions = {}

    def visit_and_pop(self, expr):
        self.visit(expr)
        return self.pop_result()

    def push_result(self, val):
        self.res.append(val)

    def pop_result(self):
        return self.res.pop()

    # visitor methods:

    def visit_BoolOp(self, e):
        operand_list = []
        for operand in e.values:
            self.visit(operand)
            operand_list.append(self.pop_result())

        bool_op = operator_ast_to_model(e.op)
        self.push_result(bool_op(operand_list))

    def visit_BinOp(self, e):
        self.visit(e.left)
        lhs = self.pop_result()

        self.visit(e.right)
        rhs = self.pop_result()

        op_func = operator_ast_to_model(e.op, self.dsl_enabled)
        zexp = op_func(lhs, rhs)
        self.push_result(zexp)

    def visit_Name(self, e):
        var = self.var_ctx.get_var_z3(e.id)
        self.push_result(var)

    def visit_Num(self, e):
        self.push_result(e.n)

    def visit_IfExp(self, e):
        test_exp = self.visit_and_pop(e.test)
        t_branch = self.visit_and_pop(e.body)
        f_branch = self.visit_and_pop(e.orelse)
        if_exp = operators.If(test_exp, t_branch, f_branch)
        self.push_result(if_exp)

    def visit_Compare(self, e):
        assert len(e.ops) == len(e.comparators)
        lhs = self.visit_and_pop(e.left)
        operands = map(self.visit_and_pop, e.comparators)
        ops = e.ops
        results = []
        for op, rhs in zip(ops, operands):
            res = operator_ast_to_model(op)(lhs, rhs)
            lhs = rhs
            results.append(res)

        self.push_result(operators.And(results))

    def visit_NameConstant(self, e):
        val = e.value
        self.push_result(val)

    def visit_Call(self, e):
        if not isinstance(e.func, ast.Name):
            raise ParseException("Only named call allowed!")

        # if self.dsl_enabled and e.func.id == 'forall_':
        #     assert len(e.args) == 2, "Forall mut contain 2 args!"
        #     res = _parse_forall(e.args[0], e.args[1], self.var_ctx)
        #     self.push_result(res)
        #     return

        unique_name = UniquePrefix(custom_prefix='call')(e.func.id)
        ret_var = self.var_ctx.functions.get(e.func.id)[0].as_z3_var(unique_name)

        inv_model = InvocationModel(e.func.id)
        for a in e.args:
            inv_model.add_arg(ExpressionModel(a))

        self.substitutions[unique_name] = (inv_model, ret_var)
        self.push_result(ret_var)

    def visit_UnaryOp(self, node):
        op_func = operator_ast_to_model(node.op, self.dsl_enabled)
        arg = self.visit_and_pop(node.operand)
        self.push_result(op_func(arg))

    def visit_Assign(self, node):
        raise Exception("Assign not allowed, use `==` to compare variables")

    def generic_visit(self, e):
        print(ast.dump(e))
        raise Exception("Nodes %s not supported" % str(e))

#
# def _parse_forall(binded_vars, body, var_ctx):
#     assert isinstance(binded_vars, ast.Dict), "Forall parsing error!"
#
#     binded_vars_ctx = VarsContext()
#     for name, var_type in zip(binded_vars.keys, binded_vars.values):
#         assert isinstance(name, ast.Name) and isinstance(var_type, ast.Name)
#         variable = type_str_to_model(var_type.id)
#         binded_vars_ctx.add_var(name.id, variable)
#
#     binded_vars_z3_ctx = binded_vars_ctx.as_z3_ctx(lambda s: "$$" + s)
#     binded_vars_z3_ctx.parent_context = var_ctx
#
#     expr_parser = ExprParser(binded_vars_z3_ctx, dsl=True)
#     res = expr_parser.parse_expr_node(body)
#     return operators.ForAll(binded_vars_z3_ctx.get_z3_var_list(), res)
