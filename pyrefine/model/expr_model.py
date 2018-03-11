
class ExpressionModel:
    def __init__(self, expr_ast):
        self.expr_ast = expr_ast

    def __repr__(self):
        attrs_str = map(lambda kv: "{!s}: {!s}".format(*kv), self.__dict__.items())
        return "{}({})".format(self.__class__.__name__, list(attrs_str))