from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    a = Symbol(complex=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.NeAbs_0.of.Ne_0.apply(Eq[0])

    Eq << Nat.Gt_0.of.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-18
