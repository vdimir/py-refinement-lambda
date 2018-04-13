import ast

from pyrefine.exceptions import PyrefineException

from pyrefine.ast_parser.funcdef_parser import get_func_def_models
from pyrefine.checker.funcdef_checker import check_func_model
from collections import OrderedDict as odict


class CheckedFunc:
    def __init__(self, err=None):
        self.err = err
        self.child = []

    def is_ok(self):
        return self.err is None


def check_program(program, raise_exception=True):
    if isinstance(program, str):
        program = ast.parse(program)

    results = odict()

    functions = {}
    func_models = get_func_def_models(program)
    for fm in func_models:
        try:
            local_functions = check_func_model(fm, functions)
        except PyrefineException as e:
            results[fm.func_name] = CheckedFunc(e)
            if raise_exception:
                raise e
            continue
        functions[fm.func_name] = fm
        results[fm.func_name] = CheckedFunc()
        results[fm.func_name].child = list(local_functions.values.keys())
    return results
