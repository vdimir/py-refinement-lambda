from collections import OrderedDict as odict
from pyrefine.exceptions import VariableNotFoundException, CheckerException
from pyrefine.helpers import merge_dict
from pyrefine.model.types import ModelVar


class ScopedContext:
    def __init__(self, values=None, scope_const=None, parent=None):
        if values is None:
            values = {}
        self.parent = parent
        self.scope_const = scope_const
        self.values = odict(values)

    def add(self, name, val):
        if name in self.values:
            raise CheckerException(reason='Variable `{}` already defined.'.format(name))
        self.values[name] = val

    def get(self, name):
        if name not in self.values:
            if self.parent is None:
                raise VariableNotFoundException(var_name=name)
            return self.parent.get(name)
        return self.values[name], self.scope_const

    def append(self, new_ctx):
        assert new_ctx.parent is None
        assert new_ctx.scope_const is None
        merge_dict(self.values, new_ctx.values)

    def __contains__(self, name):
        if name in self.values:
            return True
        if self.parent is None:
            return False
        return name in self.parent

class VarsContext:
    def __init__(self, variables=None, parent_ctx=None, name_map=None):
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

    def __contains__(self, item):
        return item in self.variables

    def get_var_z3(self, name):
        variable, name_map = self.variables.get(name)
        if name_map is not None:
            target_name = name_map(name)
        else:
            target_name = name
        return variable.as_z3_var(target_name)

    def merge(self, new_ctx):
        self.variables.append(new_ctx.variables)
        self.functions.append(new_ctx.functions)

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)

