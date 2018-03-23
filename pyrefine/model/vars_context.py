from collections import OrderedDict as odict

from pyrefine.model.types import ModelVar
from typing import Tuple


class ScopedContext:
    def __init__(self, values=None, scope_const=None, parent=None):
        if values is None:
            values = {}
        self.parent = parent
        self.scope_const = scope_const
        self.values = odict(values)

    def add(self, name, val):
        assert name not in self.values
        self.values[name] = val

    def get(self, name):
        if name not in self.values:
            if self.parent is None:
                raise VariableNotFoundException(var_name=name)
            return self.parent.get(name)
        return self.values[name], self.scope_const


class VarsContext:
    def __init__(self, variables=None, parent_ctx=None, name_map=lambda x: x):
        if parent_ctx is not None:
            vars_parent = parent_ctx.variables
            func_parent = parent_ctx.functions
        else:
            vars_parent, func_parent = None, None

        self.variables = ScopedContext(values=variables,
                                       scope_const=name_map,
                                       parent=vars_parent)
        self.functions = ScopedContext(parent=func_parent)

    def add_var(self, name: str, variable_type: ModelVar):
        self.variables.add(name, variable_type)
        return self

    def get_var_z3(self, name):
        variable, name_map = self.variables.get(name)
        target_name = name_map(name)
        return variable.as_z3_var(target_name)

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)


class VariableNotFoundException(Exception):
    def __init__(self, var_name):
        self.var_name = var_name

    def __str__(self):
        return "Variable %s not found" % self.var_name