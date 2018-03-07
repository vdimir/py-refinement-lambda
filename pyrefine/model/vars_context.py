import z3


class VarsContext:
    def __init__(self):
        self.var_sort = {}

    def add_var(self, name, sort):
        self.var_sort[name] = sort
        return self

    def add_list(self, variables):
        for n, s in variables:
            self.add_var(n, s)

    def get_var(self, name):
        return z3.Const(name, self.var_sort[name]())
