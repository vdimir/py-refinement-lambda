
import ast

from pyrefine.ast_parser.lambda_parser import DEFINE_LAMBDA_MACROS_NAME, parse_lambda_node
from pyrefine.ast_parser.mapping import type_str_to_model

from .. import model
from pyrefine.model import ExpressionModel

from pyrefine.exceptions import ParseException, CheckerException

from typing import List, Tuple, Dict


def get_assign_expr_model(program_ast,
                          defined_functions: Dict[str, model.LambdaModel],
                          strict=False):
    if strict:
        assign_visitor = StrictAssignVisitor()
    else:
        assign_visitor = AssignExprVisitor()
    assign_visitor.defined_functions = defined_functions
    assign_visitor.visit(program_ast)
    return assign_visitor.result


CHECK_ASSIGN_MACRO_NAME = 'c_'


class AssignExprVisitor(ast.NodeVisitor):
    def __init__(self):
        self.result = []
        self.defined_functions = None
        self.cur_lineno = None

    def visit_Assign(self, node: ast.Assign):
        self.cur_lineno = node.lineno

        if len(node.targets) != 1:
            raise ParseException("Multiple assign not supported.")
        if isinstance(node.targets[0], ast.Tuple):
            assert isinstance(node.value, ast.Tuple)
            assert len(node.targets[0].elts) == len(node.value.elts)
            assert all(map(lambda t: isinstance(t, ast.Name), node.targets[0].elts))
            for t, v in zip(node.targets[0].elts, node.value.elts):
                assign_model = self.process_assign(t.id, v)
                if assign_model is not None:
                    self.result.append(assign_model)
            return

        if not isinstance(node.targets[0], ast.Name):
            return

        target_name = node.targets[0].id
        assign_model = self.process_assign(target_name, node.value)
        if assign_model is not None:
            self.result.append(assign_model)

    def process_assign(self, target_name, value):
        assign_to_call = isinstance(value, ast.Call) and \
                         isinstance(value.func, ast.Name)

        if not assign_to_call:
            return target_name, None, ExpressionModel(value)

        func_name_defined = value.func.id in self.defined_functions
        if func_name_defined:
            invoke_model, ret_type = self._parse_defined_call(value)
            return target_name, ret_type, invoke_model

        if value.func.id not in [CHECK_ASSIGN_MACRO_NAME, DEFINE_LAMBDA_MACROS_NAME]:
            raise CheckerException(reason="Function {} not defined".format(value.func.id),
                                   src_info={'lineno', self.cur_lineno})

        if value.func.id == DEFINE_LAMBDA_MACROS_NAME:
            return target_name, 'FUNCTION', parse_lambda_node(value, target_name)

        if len(value.args) == 1:
            body = value.args[0]
            if isinstance(body, ast.Call):
                invoke_model, ret_type = self._parse_defined_call(body)
                return target_name, ret_type, invoke_model
            else:
                raise CheckerException(reason="Cannot infer type. "
                                              "Try to scecify it explicit.",
                                       src_info={'lineno', self.cur_lineno})

        if len(value.args) != 2:
            raise ParseException(reason="{} should have one or two arguments."
                                 .format(CHECK_ASSIGN_MACRO_NAME),
                                 src_data={'lineno', self.cur_lineno})

        if not isinstance(value.args[0], ast.Str):
            raise ParseException(reason="First argument should "
                                        "be string representing type.",
                                 src_data={'lineno', self.cur_lineno})

        ret_type = type_str_to_model(value.args[0].s)
        return target_name, ret_type, ExpressionModel(value.args[1])

    def _parse_defined_call(self, node):
        call_model = model.InvocationModel(func_name=node.func.id)
        call_model.src_data["lineno"] = node.lineno

        for arg_ast in node.args:
            call_model.add_arg(ExpressionModel(arg_ast))

        ret_type = self.defined_functions[call_model.func_name].args['ret']
        return call_model, ret_type


class StrictAssignVisitor(AssignExprVisitor):
    def generic_visit(self, node):
        raise Exception("{} not allowed".format(type(node)))
