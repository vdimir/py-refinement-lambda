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


def merge_dict(dict1, dict2):
    for k, v in dict2.items():
        if k in dict1:
            if dict1[k] == v:
                continue
            raise Exception("Key in merged dict should not intersect.")
        dict1[k] = v
    return dict1