

class InvocationModel:
    def __init__(self, func_name):
        self.func_name = func_name
        self.args = []
        self.src_data = {}

    def add_arg(self, arg):
        self.args.append(arg)

    def __str__(self):
        attrs_str = map(lambda kv: "{!s}: {!s}".format(*kv), self.__dict__.items())
        return "{}({})".format(self.__class__.__name__, list(attrs_str))
