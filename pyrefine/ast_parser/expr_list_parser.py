import ast


def get_expr_to_check(program):
    visitor = ExprListVisitor()
    visitor.visit(program)
    return visitor.result


class ExprListVisitor(ast.NodeVisitor):
    def __init__(self):
        self.result = {}

    def visit_Module(self, e):
        expr = self._get_assign(e)
        self.result['_module'] = expr

    def visit_FunctionDef(self, e):
        expr = self._get_assign(e)
        self.result[e.name] = expr

    def _get_assign(self, e):
        expr_to_check = []
        for expr in e.body:
            if isinstance(expr, ast.Assign):
                expr_to_check.append(expr)
            else:
                self.visit(expr)
        return expr_to_check