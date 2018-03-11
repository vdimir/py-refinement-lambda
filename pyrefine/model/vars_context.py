from collections import OrderedDict as odict

from pyrefine.model.types import ModelVar


class VarsContext:
    def __init__(self, variables=list()):
        self.variables = odict(variables)

    def add_var(self, name: str, variable_type: ModelVar):
        assert name not in self.variables
        self.variables[name] = variable_type
        return self

    def get_var(self, name) -> ModelVar:
        return self.variables.get(name)

    def as_z3_ctx(self, map_func=None):
        res = VarsZ3Context(self)
        res.set_rename_map(map_func)
        return res

    def __len__(self):
        return len(self.variables)

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)


class VarsZ3Context:
    def __init__(self, var_ctx: VarsContext):
        self.var_ctx = var_ctx
        self.rename_var_map = None
        self.parent_context = None

    def set_rename_map(self, func):
        self.rename_var_map = func

    def _rename_to_z3(self, name):
        if self.rename_var_map is None:
            return name
        if callable(self.rename_var_map):
            return self.rename_var_map(name)
        if isinstance(self.rename_var_map, dict):
            return self.rename_var_map[name]
        assert False, "Unreachable code"

    def get_var_z3(self, name):
        res = self.var_ctx.get_var(name)
        if res is None:
            if self.parent_context is not None:
                return self.parent_context.get_var_z3(name)
            raise VariableNotFoundException("Var %s not found" % name)

        z3_name = self._rename_to_z3(name)
        return res.as_z3_var(z3_name)

    def get_z3_var_list(self):
        return list(map(self.get_var_z3, self.var_ctx.variables.keys()))


class VariableNotFoundException(Exception):
    pass
