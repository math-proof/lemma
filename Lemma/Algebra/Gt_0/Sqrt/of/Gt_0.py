from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(sqrt(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(Greater(x, 0))

    Eq << Algebra.Ge_0.of.Gt_0.apply(Eq[0])

    Eq << Algebra.GeSqrt_0.of.Ge_0.apply(Eq[-1])

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Algebra.Sqrt.ne.Zero.of.Ne_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.of.Ne_0.Ge_0.apply(Eq[-1], Eq[-3])





if __name__ == '__main__':
    run()
# created on 2018-07-17
# updated on 2025-04-20
