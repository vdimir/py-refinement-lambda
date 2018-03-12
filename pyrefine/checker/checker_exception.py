

class CheckerException(Exception):
    pass


class LambdaDefinitionException(CheckerException):
    def __init__(self, src_info, name):
        self.src_info = src_info
        self.name = name
