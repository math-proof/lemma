from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Equal(sign(x), 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(complex=True)
    Eq << apply(x > 0)

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[0])

    Eq << Eq[1].lhs.this.apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Bool.Imp.of.Cond_Ite.apply(Eq[-1], 1)

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[-1], Eq[-2])





if __name__ == '__main__':
    run()
# created on 2023-05-29
# updated on 2025-04-20
