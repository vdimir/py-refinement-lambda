
import ast

from pyrefine.model import ExpressionModel, VarsContext

from .mapping import type_str_to_model
from .expr_parser import str_to_ast
from .. import model
from typing import List
import pyparsing as prs
from collections import OrderedDict as odict
from pyrefine.exceptions import ParseException, CheckerException

DEFINE_LAMBDA_MACROS_NAME = 'define_'
RET_VAR_NAME_MACRO = 'ret'


def get_lambdas_model(program_ast) -> odict:
    lambda_visitor = LambdaVisitor()
    lambda_visitor.visit(program_ast)
    lambda_models = lambda_visitor.result
    lambda_models_dict = odict(map(lambda m: (m.func_name, m), lambda_models))
    return lambda_models_dict


class LambdaParser:
    def __init__(self):
        pass

    def parse_lambda_node(self, node, func_name) -> model.LambdaModel:
        type_def, pre_cond, post_cond, func = node.args
        arg_names = list(map(lambda a: a.arg, func.args.args))

        arg_types = self.parse_type_def_str(type_def.s)
        if any(map(lambda v: isinstance(v, model.types.FuncVar), arg_types)):
            raise CheckerException(reason="Higher order function not supported!",
                                   src_info={'lineno': node.lineno})
        if len(arg_types) != len(arg_names) + 1:
            raise ParseException(reason="Function annotation mismatch (at: %d)"
                                        % node.lineno)

        arg_names.append(RET_VAR_NAME_MACRO)

        args = odict(zip(arg_names, arg_types))
        lambda_model = model.LambdaModel(name=func_name,
                                         args=args,
                                         body=ExpressionModel(func.body))

        lambda_model.add_pre_cond(str_to_ast(pre_cond.s))
        lambda_model.add_post_cond(str_to_ast(post_cond.s))
        lambda_model.src_data['lineno'] = node.lineno
        return lambda_model

    def parse_type_def_str(self, typedef_str: str) -> List[model.types.ModelVar]:
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
                    [func.add_arg(a) for a in args]
                    yield func
                else:
                    assert False, "Unreachable code"

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