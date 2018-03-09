
import ast
from .mapping import type_str_to_model
from .expr_parser import ExprParser
from .. import model
import typing
import pyparsing as prs


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

        arg_types = self.parse_type_def_str(type_def.s)

        assert len(arg_types) == len(arg_names) + 1, (
            "Function annotation mismatch (at: %d)" % node.lineno)

        arg_names.append(RETURN_VARIABLE_NAME)
        var_ctx = model.VarsContext()
        var_ctx.add_list(zip(arg_names, arg_types))

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

        lpar = prs.Literal('(').suppress()
        rpar = prs.Literal(')').suppress()
        arr = prs.Literal('->').suppress()
        term = prs.Word(prs.alphas)
        func_def = prs.Forward()
        typ = term | prs.Group(lpar + func_def + rpar)
        func_def << typ + prs.ZeroOrMore(arr + typ)
        func_def += prs.StringEnd()
        res = func_def.parseString(typedef_str).asList()

        def unroll(lst):
            for t in lst:
                if isinstance(t, str):
                    yield type_str_to_model(t)
                elif isinstance(t, list):
                    args = unroll(t)
                    func = model.types.FuncVar()
                    for a in args:
                        func.add_arg(a)
                    yield func
                else:
                    assert False

        return list(unroll(res))


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

