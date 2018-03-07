import ast
from collections import deque

from .mapping import operator_ast_to_model
from ..model import operators
from ..model import VarsContext


class ExprParser:
    def __init__(self, var_ctx: VarsContext):
        self.var_ctx = var_ctx

    def parse_expr_node(self, expr_node):
        expr_visitor = ExprVisitor(self.var_ctx)
        expr_visitor.visit(expr_node)
        assert len(expr_visitor.res) == 1
        return expr_visitor.pop_result()

    def parse_expr_str(self, expr_str):
        exp_ast = ast.parse(expr_str).body
        assert len(exp_ast) == 1, "Wrong expr in cond!"
        exp_ast = exp_ast[0].value
        expr_visitor = ExprVisitor(self.var_ctx)
        expr_visitor.visit(exp_ast)
        assert len(expr_visitor.res) == 1
        return expr_visitor.pop_result()


class ExprVisitor(ast.NodeVisitor):
    def __init__(self, var_ctx: VarsContext):
        self.res = deque()
        self.context = var_ctx

    def visit_and_pop(self, expr):
        self.visit(expr)
        return self.pop_result()

    def push_result(self, val):
        self.res.append(val)

    def pop_result(self):
        return self.res.pop()

    def get_final_result(self):
        res = self.pop_result()
        assert len(self.res) == 0
        return res

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

        op_func = operator_ast_to_model(e.op)
        zexp = op_func(lhs, rhs)
        self.push_result(zexp)

    def visit_Name(self, e):
        var = self.context.get_var(e.id)
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

    def generic_visit(self, e):
        print(ast.dump(e))
        raise Exception("Nodes %s not supported" % str(e))
