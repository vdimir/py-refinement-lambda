from collections import OrderedDict as odict
from pyrefine.exceptions import VariableNotFoundException, CheckerException
from pyrefine.helpers import merge_dict, UniquePrefix, generate_uid
from pyrefine.model.types import ModelVar


class ScopedContext:
    def __init__(self, parent=None):
        self.parent = parent
        self.values = odict()

    def add(self, name, val):
        if name in self.values:
            raise CheckerException(reason='Variable `{}` already defined.'.format(name))
        self.values[name] = val

    def update(self, name, val):
        if name not in self:
            raise VariableNotFoundException(var_name=name)
        self.values[name] = val

    def get(self, name):
        if name not in self.values:
            if self.parent is None:
                raise VariableNotFoundException(var_name=name)
            return self.parent.get(name)
        return self.values[name]

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

    def __repr__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)


class VarsContextBase:
    def __init__(self, variables=None, parent_ctx=None):
        if parent_ctx is not None:
            vars_parent = parent_ctx.variables
            func_parent = parent_ctx.functions
        else:
            vars_parent, func_parent = None, None

        self.variables = ScopedContext(parent=vars_parent)
        self.functions = ScopedContext(parent=func_parent)
        if variables is None:
            variables = {}

        for n, v in variables.items():
            self.add_var(n, v)

    def add_var(self, *args):
        raise NotImplementedError("Abstract method call")

    def __contains__(self, item):
        return item in self.variables

    def get_var_z3(self, name):
        variable = self.variables.get(name)
        return variable

    def __getitem__(self, name):
        return self.get_var_z3(name)

    def merge(self, new_ctx):
        self.variables.append(new_ctx.variables)
        self.functions.append(new_ctx.functions)

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)


def new_name_for_var(name):
    return "{}${}".format(name, generate_uid())


# class VarsContext(VarsContextBase):
#     def __init__(self, variables=None, parent_ctx=None, name_map=None):
#         self.name_map = name_map
#         if name_map is None:
#             self.name_map = lambda x: x
#         super().__init__(variables, parent_ctx)
#
#     def add_var(self, name: str, variable_type: ModelVar):
#         self.variables.add(
#             name, variable_type.as_z3_var(self.name_map(name)))
#         return self


class VarsContext(VarsContextBase):
    def __init__(self, variables=None, parent_ctx=None, name_map=None):
        self.name_map = name_map
        if name_map is None:
            self.name_map = lambda x: x
        super().__init__(variables, parent_ctx)

    def add_var(self, name: str, variable_type: ModelVar):
        self.variables.add(
            name, (variable_type, variable_type.as_z3_var(self.name_map(name))))
        return self

    def update(self, name: str):
        variable_type, _ = self.variables.get(name)
        self.variables.update(
            name, (variable_type, variable_type.as_z3_var(new_name_for_var(name))))
        return self

    def later_update(self, name: str):
        variable_type, _ = self.variables.get(name)
        return variable_type.as_z3_var(new_name_for_var(name))

    def later_update_finish(self, name: str, val):
        variable_type, _ = self.variables.get(name)
        self.variables.update(
            name, (variable_type, val))
        return self

    def get_var_z3(self, name):
        _, z3_variable = self.variables.get(name)
        return z3_variable

    def get_var_type(self, name):
        if name in self.functions:
            return self.functions.get(name)

        if name in self.variables:
            model_type, _ = self.variables.get(name)
            return model_type


