
import ast
from .mapping import type_str_to_model
from .expr_parser import ExprParser
from .. import model
import typing
import pyparsing as prs


DEFINE_LAMBDA_MACROS_NAME = 'define_'
RETURN_VARIABLE_NAME_MACRO = 'ret'


def get_lambdas_model(program_ast) -> typing.List[model.LambdaModel]:
    lambda_visitor = LambdaVisitor()
    lambda_visitor.visit(program_ast)
    return lambda_visitor.result


class LambdaParser:
    def __init__(self):
        pass

    def parse_lambda_node(self, node, func_name) -> model.LambdaModel:
        type_def, pre_cond, post_cond, func = node.args
        arg_names = list(map(lambda a: a.arg, func.args.args))

        arg_types = self.parse_type_def_str(type_def.s)

        assert len(arg_types) == len(arg_names) + 1, (
            "Function annotation mismatch (at: %d)" % node.lineno)

        var_ctx = model.VarsContext()
        for var_name, variable in zip(arg_names, arg_types):
            variable.set_name("{}${}".format(func_name, var_name))
            var_ctx.add_var(var_name, variable)

        arg_types[-1].set_name("{}${}".format(func_name, RETURN_VARIABLE_NAME_MACRO))
        var_ctx.add_var(RETURN_VARIABLE_NAME_MACRO, arg_types[-1])

        expr_parser = ExprParser(var_ctx, dsl=True)
        pre_cond = expr_parser.parse_expr_str(pre_cond.s)
        post_cond = expr_parser.parse_expr_str(post_cond.s)

        expr_parser = ExprParser(var_ctx, dsl=False)
        func_body_model = expr_parser.parse_expr_node(func.body)

        lambda_model = model.LambdaModel(args=var_ctx,
                                         body=func_body_model,
                                         ret_var_name=RETURN_VARIABLE_NAME_MACRO)
        lambda_model.set_name(func_name)
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
        if not is_assign_lambda_def(node):
            return

        if len(node.value.args) != 4:
            raise Exception("Wrong number of args!")

        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            raise Exception("Wrong assign!")

        target_func_name = node.targets[0].id

        prs = LambdaParser()
        lambda_model = prs.parse_lambda_node(node.value, target_func_name)

        self.result.append(lambda_model)


def is_assign_lambda_def(node):
    if not isinstance(node.value, ast.Call):
        return False

    if not isinstance(node.value.func, ast.Name):
        return False

    if node.value.func.id != DEFINE_LAMBDA_MACROS_NAME:
        return False

    return True