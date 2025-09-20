from util import *


@apply
def apply(eq, ne):

    a, x = eq.of(Equal)
    _x, b = ne.of(Unequal)
    if x != _x:
        if _x == a:
            a, x = x, a

        assert x == _x
    return Unequal(a, b)


@prove
def prove(Eq):
    x, y, a = Symbol(etype=dtype.integer)
    Eq << apply(Equal(x, y), Unequal(y, a))

    Eq << Eq[1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2020-02-11

from . import subst
