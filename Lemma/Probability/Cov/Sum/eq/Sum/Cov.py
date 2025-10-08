from util import *


@apply
def apply(self, deep=False):
    lhs, rhs = self.of(Covariance)
    if lhs.is_Sum:
        if rhs.is_Sum and deep:
            sgm = []
            expr_l, *limits_l = lhs.args
            expr_r, *limits_r = rhs.args
            rhs = Sum(Covariance(expr_l, expr_r), *limits_l, *limits_r)
        else:
            expr, *limits = lhs.args
            rhs = Sum(Covariance(expr, rhs), *limits)
    elif rhs.is_Sum:
        expr, *limits = rhs.args
        rhs = Sum(Covariance(lhs, expr), *limits)
    else:
        return
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool

    x = Symbol(real=True, random=True)
    y = Symbol(real=True, shape=(oo,), random=True)
    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Covariance(x, Sum[k:n](y[k])))

    Eq << Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Probability.Cov.Add.eq.Add.Cov)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n, 1)


if __name__ == '__main__':
    run()
# created on 2023-04-19
