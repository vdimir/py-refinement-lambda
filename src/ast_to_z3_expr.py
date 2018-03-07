"""Convert python expression presented in AST to Z3 expression."""

import ast
import operator
import z3

from collections import deque

ast_to_z3_op = {
    ast.FloorDiv: operator.truediv,
    ast.And: z3.And,
    ast.Add: operator.add,
    ast.Mult: operator.mul,
    ast.Or: z3.Or,
    ast.Eq: operator.eq,
    ast.Gt: operator.gt,
    ast.GtE: operator.ge,
    ast.Lt: operator.lt,
    ast.LtE: operator.le,
}


class ExpToZ3(ast.NodeVisitor):
    def __init__(self, z3_ctx):
        self.res = deque()
        self.context = z3_ctx

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

        bool_op = ast_to_z3_op[type(e.op)]
        self.push_result(bool_op(operand_list))

    def visit_BinOp(self, e):
        self.visit(e.left)
        lhs = self.pop_result()

        self.visit(e.right)
        rhs = self.pop_result()

        zexp = ast_to_z3_op[type(e.op)](lhs, rhs)
        self.push_result(zexp)

    def visit_Name(self, e):
        var = self.context[e.id]
        self.push_result(var)

    def visit_Num(self, e):
        self.push_result(e.n)

    def visit_IfExp(self, e):
        test_exp = self.visit_and_pop(e.test)
        t_branch = self.visit_and_pop(e.body)
        f_branch = self.visit_and_pop(e.orelse)
        if_exp = z3.If(test_exp, t_branch, f_branch)
        self.push_result(if_exp)

    def visit_Compare(self, e):
        assert len(e.ops) == len(e.comparators)
        lhs = self.visit_and_pop(e.left)
        operands = map(self.visit_and_pop, e.comparators)
        ops = e.ops
        results = []
        for op, rhs in zip(ops, operands):
            res = ast_to_z3_op[type(op)](lhs, rhs)
            lhs = rhs
            results.append(res)

        self.push_result(z3.And(results))

    def visit_NameConstant(self, e):
        val = e.value
        self.push_result(val)

    def generic_visit(self, e):
        print(ast.dump(e))
        raise Exception("Nodes %s not supported" % str(e))
