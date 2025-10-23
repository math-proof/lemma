from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[0])

    Eq << Nat.Ne.of.Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
# updated on 2025-04-20
