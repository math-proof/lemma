from util import *


@apply
def apply(is_positive, is_nonpositive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    m = is_nonpositive.of(Expr <= 0)
    if x is None:
        x = m.generate_var(M.free_symbols, real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, m <= 0, x=x)

    Eq << Logic.Imp_And.of.Cond.apply(Eq[0], cond=m < 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Inf_Square.eq.Zero.of.Gt_0.Lt_0)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[2], cond=m < 0)

    Eq << Logic.Imp_And.of.Cond.apply(Eq[0] & Eq[1], cond=m >= 0)

    Eq << Eq[-1].this.rhs.args[1:].apply(Algebra.Eq.of.Le.Ge)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Inf_Square.eq.Zero.of.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq.subst.lhs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2019-08-25
# updated on 2023-05-20
