import uuid


class UniquePrefix:
    def __init__(self, prefix_len=4, custom_prefix=''):
        self.prefix = str(uuid.uuid4().hex[:prefix_len])
        self.custom_prefix = custom_prefix

    def __call__(self, s: str):
        return "${}${}${}".format(self.custom_prefix, self.prefix, s)


class SimplePrefix:
    def __init__(self, custom_prefix=''):
        self.custom_prefix = custom_prefix

    def __call__(self, s: str):
        return "${}${}".format(self.custom_prefix, s)
