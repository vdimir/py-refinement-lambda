from .vars_context import VarsContext


class LambdaModel:
    def __init__(self, args: VarsContext, body, ret_var_name):
        self.variables = args
        self.body = body
        self.pre_cond = None
        self.post_cond = None
        self.ret_var_name = ret_var_name

        self.src_data = {}

    def add_pre_cond(self, pre_cond):
        self.pre_cond = pre_cond

    def add_post_cond(self, post_cond):
        self.post_cond = post_cond
