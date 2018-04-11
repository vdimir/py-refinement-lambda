from .lambda_parser import is_assign_lambda_def


def is_node_auxilary(node):
    if is_assign_lambda_def(node):
        return True
    return False
