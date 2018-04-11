import ast

from pyrefine.exceptions import PyrefineException

from pyrefine.ast_parser.funcdef_parser import get_func_def_models
from pyrefine.checker.funcdef_checker import check_func_model
from collections import OrderedDict as odict


def check_program(program, raise_exception=True):
    if isinstance(program, str):
        program = ast.parse(program)

    results = odict()

    functions = {}
    func_models = get_func_def_models(program)
    for fm in func_models:
        try:
            check_func_model(fm, functions.copy())
        except PyrefineException as e:
            results[fm.func_name] = e
            if raise_exception:
                raise e
            continue
        functions[fm.func_name] = fm
        results[fm.func_name] = None
    return results
