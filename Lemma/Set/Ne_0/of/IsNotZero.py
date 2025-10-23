from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False and RR in Reals
    return Unequal(x, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Set.Gt_0.Abs.of.IsNotZero.apply(Eq[0])

    Eq << Nat.Ne.of.Gt.apply(Eq[-1])

    Eq << Algebra.Ne_0.of.NeAbs_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2025-04-20
