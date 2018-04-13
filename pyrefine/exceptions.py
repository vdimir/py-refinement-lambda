class PyrefineException(Exception):
    def __init__(self, src_info=None, reason=""):
        self.reason = reason
        self.src_info = src_info
        if src_info is None:
            self.src_info = {}

    def __repr__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)

    def __str__(self):
        res_str = self.reason
        if 'lineno' in self.src_info:
            res_str += " (lineno: {})".format(self.src_info['lineno'])
        return res_str


class CheckerException(PyrefineException):
    def __init__(self, src_info=None, reason="", counterexample=None):
        self.counterexample = counterexample
        self.reason = reason
        self.src_info = src_info
        if src_info is None:
            self.src_info = {}


class LambdaDefinitionException(CheckerException):
    def __init__(self, src_info, name, counterexample=None):
        self.counterexample = counterexample
        self.src_info = src_info
        self.name = name
        self.reason = "Return constraints for {} may not hold!".format(self.name)


class WhileDefinitionException(CheckerException):
    pass


class ErrorCallException(CheckerException):
    def __init__(self, src_info, name, reason=None):
        self.reason = reason
        self.src_info = src_info
        self.name = name


class ParseException(PyrefineException):
    def __init__(self, expr_str=None, reason=None, src_data=None):
        self.src_data = src_data
        self.reason = reason
        self.expr_str = expr_str


class VariableNotFoundException(PyrefineException):
    def __init__(self, var_name):
        self.var_name = var_name

    def __str__(self):
        return "Variable %s not found" % self.var_name