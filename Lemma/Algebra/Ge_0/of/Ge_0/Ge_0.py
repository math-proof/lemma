from util import *


@apply
def apply(is_nonnegative_x, is_nonnegative_y):
    x = is_nonnegative_x.of(Expr >= 0)
    y = is_nonnegative_y.of(Expr >= 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, y >= 0)

    Eq.case0 = Imply(Equal(x, 0), x * y >= 0, plausible=True)

    Eq << Eq.case0.this.apply(Logic.IffImpSAndEq)

    Eq << Logic.Imp.of.Cond.apply(Eq[1], cond=x > 0)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.of.Gt_0.Ge_0)

    Eq <<= Eq.case0 & Eq[-1]

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()

# created on 2018-07-02
# updated on 2023-06-20

