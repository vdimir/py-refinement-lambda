from .vars_context import VarsContext


class LambdaModel:
    def __init__(self, args: VarsContext, body, ret_var_name):
        self.variables = args
        self.body = body
        self.pre_cond = None
        self.post_cond = None
        self.ret_var_name = ret_var_name
        self.func_name = None
        self.src_data = {}

    def set_name(self, name: str):
        self.func_name = name

    def add_pre_cond(self, pre_cond):
        self.pre_cond = pre_cond

    def add_post_cond(self, post_cond):
        self.post_cond = post_cond

    def __str__(self):
        attrs_str = map(lambda kv: "{}: {}".format(*kv), self.__dict__.items())
        return "{}({})".format(self.__class__.__name__, list(attrs_str))