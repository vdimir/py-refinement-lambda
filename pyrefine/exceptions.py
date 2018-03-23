class PyrefineException(Exception):
    def __str__(self):
        return "%s(%r)" % (self.__class__.__name__, self.__dict__)


class CheckerException(PyrefineException):
    pass


class LambdaDefinitionException(CheckerException):
    def __init__(self, src_info, name):
        self.src_info = src_info
        self.name = name


class ErrorCallException(CheckerException):
    def __init__(self, src_info, name, reason=None):
        self.reason = reason
        self.src_info = src_info
        self.name = name


class ParseException(PyrefineException):
    def __init__(self, expr_str=None, reason=None):
        self.reason = reason
        self.expr_str = expr_str


class VariableNotFoundException(PyrefineException):
    def __init__(self, var_name):
        self.var_name = var_name

    def __str__(self):
        return "Variable %s not found" % self.var_name