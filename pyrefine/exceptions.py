class PyrefineException(Exception):
    pass


class CheckerException(PyrefineException):
    pass


class LambdaDefinitionException(CheckerException):
    def __init__(self, src_info, name):
        self.src_info = src_info
        self.name = name


class ErrorCallException(CheckerException):
    def __init__(self, src_info, name):
        self.src_info = src_info
        self.name = name


class ParseException(PyrefineException):
    def __init__(self, expr_str=None, reason=None):
        self.reason = reason
        self.expr_str = expr_str