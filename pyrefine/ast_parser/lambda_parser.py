
import ast
from .mapping import type_str_to_model
from .expr_parser import ExprParser
from .. import model
import typing


DEFINE_LAMBDA_MACROS_NAME = 'define_'
RETURN_VARIABLE_NAME = 'ret'


def get_lambdas_model(program_ast) -> typing.List[model.LambdaModel]:
    lambda_visitor = LambdaVisitor()
    lambda_visitor.visit(program_ast)
    return lambda_visitor.result


class LambdaParser:
    def __init__(self):
        pass

    def parse_lambda_node(self, node) -> model.LambdaModel:
        type_def, pre_cond, post_cond, func = node.args
        arg_names = list(map(lambda a: a.arg, func.args.args))

        arg_types_str, ret_type_str = self.parse_type_def_str(type_def.s)

        assert len(arg_types_str) == len(arg_names), (
            "Function annotation mismatch (at: %d)" % node.lineno)

        var_ctx = model.VarsContext()
        arg_sorts_model = map(type_str_to_model, arg_types_str)
        var_ctx.add_list(zip(arg_names, arg_sorts_model))
        var_ctx.add_var(RETURN_VARIABLE_NAME, type_str_to_model(ret_type_str))

        expr_parser = ExprParser(var_ctx)
        pre_cond = expr_parser.parse_expr_str(pre_cond.s)
        post_cond = expr_parser.parse_expr_str(post_cond.s)
        func_body_model = expr_parser.parse_expr_node(func.body)

        lambda_model = model.LambdaModel(args=var_ctx,
                                         body=func_body_model,
                                         ret_var_name=RETURN_VARIABLE_NAME)

        lambda_model.add_pre_cond(pre_cond)
        lambda_model.add_post_cond(post_cond)
        lambda_model.src_data['lineno'] = node.lineno
        return lambda_model

    def parse_type_def_str(self, typedef_str: str):
        """Parse function type annotation."""
        annot = map(str.strip, typedef_str.split('->'))
        *args, ret = (list(annot))
        return args, ret


class LambdaVisitor(ast.NodeVisitor):
    """Visit lambda definition wrapped in macro."""

    def __init__(self):
        self.result = []

    def visit_Assign(self, node: ast.Assign):
        if not isinstance(node.value, ast.Call):
            return

        lambda_model = self.visit_Call(node.value)
        if lambda_model is None:
            return

        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            raise Exception("Wrong assign!")

        lambda_model.set_name(node.targets[0].id)
        self.result.append(lambda_model)

    def visit_Call(self, e) -> typing.Optional[model.LambdaModel]:
        if not isinstance(e.func, ast.Name):
            return

        if e.func.id != DEFINE_LAMBDA_MACROS_NAME:
            return

        if len(e.args) != 4:
            raise Exception("Wrong number of args!")

        prs = LambdaParser()
        lambda_model = prs.parse_lambda_node(e)
        return lambda_model

