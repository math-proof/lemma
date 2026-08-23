from util import *

def trans(cls, eq, cond):
    lhs, x = eq.of(Equal)
    _x, rhs = cond.of(cls)
    if x != _x:
        if lhs == _x:
            lhs = x
        elif x == rhs:
            lhs, rhs = _x, lhs

    return cls(lhs, rhs)

@apply
def apply(eq, cond):
    return trans(Greater, eq, cond)


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)
    Eq << apply(Equal(a, x), x > b)

    Eq << Eq[2].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-01

from . import subst
