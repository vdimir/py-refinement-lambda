from pyrefine import *

def proof():
    define_('int', 'True', 'True')
    implies = define_('bool -> bool -> bool', 'True',
                 'ret == (a >> b)',
                 lambda a, b: b if a else True)
    assert implies(False, False)
    assert implies(False, True)
    assert not implies(True, False)
    assert implies(True, True)

    # (a /\ b) -> a
    prop1 = define_('bool -> bool -> bool', 'True', 'ret',
                 lambda a, b: implies((a and b), a))
    # a -> ((a -> b) -> b)
    prop2 = define_('bool -> bool -> bool', 'True', 'ret',
                 lambda a, b: implies(a, implies(implies(a, b), a)))
    # a \/ ~a
    excluded_middle = define_('bool -> bool', 'True', 'ret',
                 lambda a: a or not a)
    # ~(a /\ b) <-> ~a \/ ~b
    de_morgan = define_('bool -> bool -> bool', 'True', 'ret',
                 lambda a, b: not (a and b) == (not a or not b))

