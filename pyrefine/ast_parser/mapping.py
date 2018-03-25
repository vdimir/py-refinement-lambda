import ast
from ..model import operators
from ..model import types

_operator_ast_to_model = {
    ast.FloorDiv: operators.truediv,
    ast.Mod: operators.mod,
    ast.And: operators.And,
    ast.Add: operators.add,
    ast.Sub: operators.sub,
    ast.Mult: operators.mul,
    ast.Or: operators.Or,
    ast.Eq: operators.eq,
    ast.NotEq: operators.ne,
    ast.Gt: operators.gt,
    ast.GtE: operators.ge,
    ast.Lt: operators.lt,
    ast.LtE: operators.le,
    ast.Not: operators.Not,
    ast.UAdd: operators.pos,
    ast.USub: operators.neg,
}

_operator_ast_to_model_dsl = {
    ast.RShift: operators.Implies,
    ast.Invert: operators.Not,
}

_type_string_to_model = {
    'int': types.IntVar,
    'bool': types.BoolVar,
}


def type_str_to_model(s) -> types.ModelVar:
    return _type_string_to_model[s]()


def operator_ast_to_model(op, allow_dsl=False):
    if not isinstance(op, type):
        op = type(op)

    if allow_dsl:
        res = _operator_ast_to_model_dsl.get(op)
        if res is not None:
            return res

    return _operator_ast_to_model[op]
