
import ast

from pyrefine.ast_parser.mapping import type_str_to_model

from .. import model
from pyrefine.model import ExpressionModel

from pyrefine.exceptions import ParseException, CheckerException

from typing import List, Tuple, Dict


def get_assign_expr_model(program_ast,
                          defined_functions: Dict[str, model.LambdaModel]) \
        -> List[Tuple[str, model.InvocationModel]]:
    invoke_visitor = AssignExprVisitor()
    invoke_visitor.defined_functions = defined_functions
    invoke_visitor.visit(program_ast)
    return invoke_visitor.result


CHECK_ASSIGN_MACRO_NAME = 'c_'


class AssignExprVisitor(ast.NodeVisitor):
    def __init__(self):
        self.result = []
        self.defined_functions = None

    def visit_Assign(self, node: ast.Assign):

        assign_to_call = isinstance(node.value, ast.Call) and \
                            isinstance(node.value.func, ast.Name)

        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            return

        target_name = node.targets[0].id

        if not assign_to_call:
            self.result.append((target_name, None, None))
            return


        func_name_defined = node.value.func.id in self.defined_functions
        if func_name_defined:
            invoke_model, ret_type = self._parse_defined_call(node.value)
            self.result.append((target_name, ret_type, invoke_model))
            return

        if node.value.func.id != CHECK_ASSIGN_MACRO_NAME:
            return

        if len(node.value.args) == 1:
            body = node.value.args[0]
            if isinstance(body, ast.Call):
                invoke_model, ret_type = self._parse_defined_call(body)
                self.result.append((target_name, ret_type, invoke_model))
                return
            else:
                raise CheckerException(reason="Cannot infer type. "
                                            "Try to scecify it explicit.",
                                       src_info={'lineno', node.lineno})

        if len(node.value.args) != 2:
            raise ParseException(reason="{} should have one or two arguments."
                                        .format(CHECK_ASSIGN_MACRO_NAME),
                                 src_data={'lineno', node.lineno})

        if not isinstance(node.value.args[0], ast.Str):
            raise ParseException(reason="First argument should "
                                        "be string representing type.",
                                 src_data={'lineno', node.lineno})

        ret_type = type_str_to_model(node.value.args[0].s)
        self.result.append((target_name, ret_type, ExpressionModel(node.value.args[1])))

    def _parse_defined_call(self, node):
        call_model = model.InvocationModel(func_name=node.func.id)
        call_model.src_data["lineno"] = node.lineno

        for arg_ast in node.args:
            call_model.add_arg(ExpressionModel(arg_ast))

        ret_type = self.defined_functions[call_model.func_name].args['ret']
        return call_model, ret_type

