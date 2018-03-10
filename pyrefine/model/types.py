import z3


class ModelVar:
    def __init__(self, name=None):
        self._name = name

    def set_name(self, name):
        self._name = name

    def gen_name_or(self, name):
        if self._name is not None:
            return self._name
        assert False, "Variable name must be set!"
        return name

    def as_z3_var(self, name):
        raise NotImplementedError("Abstract method call.")

    def get_sort(self):
        raise NotImplementedError("Abstract method call.")


class SimpleConst(ModelVar):
    def as_z3_var(self, name):
        return z3.Const(self.gen_name_or(name), self.get_sort())


class IntVar(SimpleConst):

    def get_sort(self):
        return z3.IntSort()


class BoolVar(SimpleConst):

    def get_sort(self):
        return z3.BoolSort()


class FuncVar(ModelVar):
    def __init__(self):
        super().__init__()
        self.arg_types = []

    def add_arg(self, var_type):
        assert isinstance(var_type, SimpleConst), "Higher order function not supported!"
        self.arg_types.append(var_type)

    def as_z3_var(self, name):
        func_args = map(lambda t: t.get_sort(), self.arg_types)
        return z3.Function(self.gen_name_or(name), *func_args)
