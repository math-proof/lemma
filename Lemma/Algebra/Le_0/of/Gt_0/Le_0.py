from util import *


@apply
def apply(is_positive_x, is_nonpositive_y):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(x > 0, y <= 0)

    Eq.case0 = Imply(Equal(y, 0), Eq[-1], plausible=True)

    Eq << Eq.case0.this.apply(Logic.IffImpSAndEq)

    Eq << Logic.Imp.of.Cond.apply(Eq[0], cond=y < 0)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt_0.of.Gt_0.Lt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.of.Lt)

    Eq <<= Eq.case0 & Eq[-1]

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[1], Eq[-1])




if __name__ == '__main__':
    run()

# created on 2018-02-08
# updated on 2025-04-10
