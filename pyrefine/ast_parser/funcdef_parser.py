import ast

from pyrefine.ast_parser.expr_parser import str_to_ast

from pyrefine.ast_parser.lambda_parser import DEFINE_LAMBDA_MACROS_NAME, \
    parse_type_def_str, RET_VAR_NAME_MACRO

from collections import OrderedDict as odict
from pyrefine import model

LOOP_DEF_MACRO = 'loop_'


class FunDefCollectVisitor(ast.NodeVisitor):
    def __init__(self):
        self.func_def = []

    def visit_FunctionDef(self, node):
        definition, *statement_list = node.body
        if not is_function_definition(node.body[0]):
            return

        arg_types, pre_cond, post_cond = parse_function_definition(definition.value)
        arg_names = list(map(lambda a: a.arg, node.args.args))
        arg_names.append(RET_VAR_NAME_MACRO)
        func_annotation = odict(zip(arg_names, arg_types))

        lambda_model = model.FunctionDefModel(
            name=node.name, args=func_annotation, body=statement_list)

        lambda_model.add_pre_cond(pre_cond)
        lambda_model.add_post_cond(post_cond)
        lambda_model.src_data['lineno'] = node.lineno
        self.func_def.append(lambda_model)


def is_function_definition(node):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    if node.value.func.id != DEFINE_LAMBDA_MACROS_NAME:
        return False
    for arg in node.value.args[:3]:
        if not isinstance(arg, ast.Str):
            return False
    return True


def parse_function_definition(define_node):
    type_def, pre_cond, post_cond = define_node.args[:3]
    arg_types = parse_type_def_str(type_def.s)
    pre_cond = str_to_ast(pre_cond.s)
    post_cond = str_to_ast(post_cond.s)
    return arg_types, pre_cond, post_cond


def parse_loop_definition(loop_def_node):
    if not isinstance(loop_def_node, ast.Expr):
        return None, None
    loop_def_node = loop_def_node.value
    if loop_def_node.func.id != LOOP_DEF_MACRO:
        return None, None
    inv_cond, dec_func = loop_def_node.args
    inv_cond = str_to_ast(inv_cond.s)
    dec_func = str_to_ast(dec_func.s)
    return inv_cond, dec_func


def get_func_def_models(program_ast):
    visitor = FunDefCollectVisitor()
    visitor.visit(program_ast)
    return visitor.func_def


class NameVisitor(ast.NodeVisitor):
    def __init__(self):
        self.names = []

    def visit_Name(self, node):
        self.names.append(node.id)

    @staticmethod
    def get_names(node):
        visitor = NameVisitor()
        visitor.visit(node)
        return visitor.names
