from util import *


@apply
def apply(self, deep=False):
    lhs, rhs = self.of(Covariance)
    if lhs.is_ReducedSum:
        if rhs.is_ReducedSum and deep:
            sgm = []
            i = self.generate_var(integer=True)
            j = self.generate_var(integer=True, excludes={i})
            expr_l = lhs.arg[tuple([slice(None) for _ in lhs.arg.shape[:-1]] + [i])]
            expr_r = rhs.arg[tuple([slice(None) for _ in rhs.arg.shape[:-1]] + [j])]
            rhs = Sum[j:rhs.arg.shape[-1], i:lhs.arg.shape[-1]](Covariance(expr_l, expr_r))
        else:
            i = self.generate_var(integer=True)
            expr = lhs.arg[tuple([slice(None) for _ in lhs.arg.shape[:-1]] + [i])]
            rhs = Sum[i:lhs.arg.shape[-1]](Covariance(expr, rhs))
    elif rhs.is_ReducedSum:
        j = self.generate_var(integer=True)
        expr = rhs.arg[tuple([slice(None) for _ in rhs.arg.shape[:-1]] + [j])]
        rhs = Sum[j:rhs.arg.shape[-1]](Covariance(lhs, expr))
    else:
        return
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Probability, Vector

    x = Symbol(real=True, random=True)
    y = Symbol(real=True, shape=(oo,), random=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Covariance(x, ReducedSum(y[:n])))

    Eq << Eq[0].this.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.lhs.apply(Probability.Cov.Sum.eq.Sum.Cov)


if __name__ == '__main__':
    run()
# created on 2023-04-19
