import z3


class VarsContext:
    def __init__(self):
        self.var_sort = {}

    def add_var(self, name, sort):
        assert name not in self.var_sort
        self.var_sort[name] = sort
        return self

    def add_list(self, variables):
        for n, s in variables:
            self.add_var(n, s)

    def get_var(self, name):
        return self.var_sort[name].get_z3_var(name)

    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)