import z3


class VarsContext:
    def __init__(self):
        self.parent_context = None
        self.variables = {}

    def add_var(self, name: str, variable_type):
        assert name not in self.variables
        self.variables[name] = variable_type
        return self

    def add_list(self, variables):
        for n, s in variables:
            self.add_var(n, s)

    def get_var(self, name):
        if name in self.variables:
            return self.variables[name]

        if self.parent_context is not None:
            return self.parent_context.get_var(name)
        raise Exception("Var %s not found" % name)

    def get_var_z3(self, name):
        return self.get_var(name).as_z3_var(name)

    def get_var_list(self):
        return list(map(self.get_var_z3, self.variables.keys()))

    def set_parent_context(self, ctx):
        self.parent_context = ctx

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)