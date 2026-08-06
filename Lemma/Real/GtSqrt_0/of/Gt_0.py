from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(sqrt(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Real, Nat

    x = Symbol(real=True)
    Eq << apply(Greater(x, 0))

    Eq << Nat.Ge.of.Gt.apply(Eq[0])

    Eq << Algebra.GeSqrt_0.of.Ge_0.apply(Eq[-1])

    Eq << Real.NeSqrt_0.of.Gt_0.apply(Eq[0])

    Eq << Nat.Gt.of.Ge.Ne.apply(Eq[-1], Eq[-2])



if __name__ == '__main__':
    run()
# created on 2018-07-17
# updated on 2025-04-20
