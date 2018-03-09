import ast
from ..model import operators
from ..model import types

_operator_ast_to_model = {
    ast.FloorDiv: operators.truediv,
    ast.And: operators.And,
    ast.Add: operators.add,
    ast.Mult: operators.mul,
    ast.Or: operators.Or,
    ast.Eq: operators.eq,
    ast.Gt: operators.gt,
    ast.GtE: operators.ge,
    ast.Lt: operators.lt,
    ast.LtE: operators.le,
}

_type_string_to_model = {
    'int': types.IntVar,
    'bool': types.BoolVar,
}


def type_str_to_model(s):
    return _type_string_to_model[s]()


def operator_ast_to_model(op):
    if not isinstance(op, type):
        op = type(op)
    return _operator_ast_to_model[op]
