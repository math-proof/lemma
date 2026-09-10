from util import *


@apply
def apply(ne, NotIn):
    _x, y = ne.of(Unequal)
    x, s = NotIn.of(NotElement)

    if x != _x:
        S[x], y = y, _x

    return NotElement(x, s | y.set)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(integer=True, given=True)
    s = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), NotElement(x, s))

    Eq << Set.NotIn.of.Ne.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[1]




if __name__ == '__main__':
    run()
# created on 2023-05-20
