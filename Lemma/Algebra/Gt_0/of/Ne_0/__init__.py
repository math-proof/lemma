from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x >= 0
    return Greater(x, 0)


@prove
def prove(Eq):
    from Lemma import Set
    a = Symbol(real=True, nonnegative=True)

    Eq << apply(Unequal(a, 0))

    Eq << Element(a, Interval(0, oo), plausible=True)

    Eq << Set.NotIn.of.Ne.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-03-17

from . import Ge_0
