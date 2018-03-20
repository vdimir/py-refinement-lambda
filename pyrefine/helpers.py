import uuid


class UniquePrefix:
    def __init__(self, prefix_len=8):
        self.prefix = str(uuid.uuid4().hex[:prefix_len])
        self.custom_prefix = ''

    def __call__(self, s: str):
        return "$uid{}${}${}".format(self.prefix, self.custom_prefix, s)
