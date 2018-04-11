import uuid


class UniquePrefix:
    def __init__(self, prefix_len=4, custom_prefix=''):
        self.prefix = generate_uid(prefix_len)
        self.custom_prefix = custom_prefix

    def __call__(self, s: str):
        return "{}${}".format(s, self.prefix)


def generate_uid(length=8):
    return str(uuid.uuid4().hex[:length])

# GLOBAL = 0
# def generate_uid(length=8):
#     global GLOBAL
#     GLOBAL += 1
#     return str(GLOBAL)

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
            raise ValueError("Key in merged dict should not intersect.")
        dict1[k] = v
    return dict1


def accepts(*types):
    def check_accepts(f):
        def new_f(*args, **kwds):
            for (a, t) in zip(args, types):
                if t is None:
                    continue
                assert isinstance(a, t), \
                       "arg %r does not match %s" % (a,t)
            return f(*args, **kwds)
        return new_f
    return check_accepts
