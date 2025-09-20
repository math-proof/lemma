from util import *


@apply
def apply(ne, cond):
    old, new = ne.of(Unequal)
    old, new = KroneckerDelta(old, new), S.Zero

    return ne, cond._subs(old, new)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Unequal(x, y), NotElement(KroneckerDelta(x, y) + f(x), S))

    Eq << Algebra.Eq_0.Delta.of.Ne.apply(Eq[0], simplify=None)

    Eq << Eq[1].subs(Eq[-1])







if __name__ == '__main__':
    run()
# created on 2019-05-03
# updated on 2023-08-26
