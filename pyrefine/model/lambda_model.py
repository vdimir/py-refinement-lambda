from pyrefine.model import types
from pyrefine.model.expr_model import ExpressionModel
from pyrefine.model.types import SimpleConst

from .vars_context import VarsContext


class LambdaModel:
    def __init__(self, name, args, body: ExpressionModel):
        self.func_name = name
        self.args = args
        self.body = body
        self._pre_cond = None
        self._post_cond = None
        self.src_data = {}

    @property
    def pre_cond(self) -> ExpressionModel:
        return self._pre_cond

    @property
    def post_cond(self) -> ExpressionModel:
        return self._post_cond

    @property
    def arity(self):
        return len(self.args) - 1

    def add_pre_cond(self, pre_cond: ExpressionModel):
        self._pre_cond = pre_cond

    def add_post_cond(self, post_cond: ExpressionModel):
        self._post_cond = post_cond

    def __str__(self):
        attrs_str = map(lambda kv: "{}: {}".format(*kv), self.__dict__.items())
        return "{}({})".format(self.__class__.__name__, list(attrs_str))