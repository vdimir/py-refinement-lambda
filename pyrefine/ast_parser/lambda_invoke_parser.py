
import ast

from .. import model
from pyrefine.model import ExpressionModel
from pyrefine.ast_parser.expr_parser import expr_model_to_z3

from typing import List, Tuple, Dict


def get_invocations_model(program_ast,
                          defined_functions: Dict[str, model.LambdaModel]) \
        -> List[Tuple[str, model.InvocationModel]]:
    invoke_visitor = TopLevelInvokeVisitor()
    invoke_visitor.defined_functions = defined_functions
    invoke_visitor.visit(program_ast)
    return invoke_visitor.result


class TopLevelInvokeVisitor(ast.NodeVisitor):
    def __init__(self):
        self.result = []
        self.defined_functions = None

    def visit_Assign(self, node: ast.Assign):
        if not isinstance(node.value, ast.Call):
            return

        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            return

        name_defined = node.value.func.id in self.defined_functions

        if not name_defined:
            return

        target_name = node.targets[0].id
        invoke_model = self._visit_Call(node.value)
        self.result.append((target_name, invoke_model))

    def _visit_Call(self, node):
        call_model = model.InvocationModel(func_name=node.func.id)
        call_model.src_data["lineno"] = node.lineno
        call_model.lambda_model = self.defined_functions[node.func.id]

        for arg_ast in node.args:
            # call_model.add_arg(v.visit(arg_ast))
            call_model.add_arg(ExpressionModel(arg_ast))
        return call_model


# class FuncInvokeVisitor(ast.NodeVisitor):
#     def __init__(self):
#         pass
#
#     def generic_visit(self, node):
#         return node
#
#     def visit_Call(self, node):
#         call_model = model.InvocationModel(func_name=node.func.id)
#         for arg_ast in node.args:
#             call_model.add_arg(self.visit(arg_ast))
#
#         return call_model
