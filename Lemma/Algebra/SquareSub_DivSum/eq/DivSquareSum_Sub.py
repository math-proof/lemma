from util import *


@apply
def apply(self):
    y, x, i, n = dissect_variance(self)
    return Equal(self, Sum[i:n](y - x[i]) ** 2 / n ** 2)


def dissect_distance(variance):
    ym, x_mean = variance.of(Abs[Expr - Expr])
    x_sum, n = x_mean.of(Expr / Expr)
    xi, (i, *ab) = x_sum.of(Sum)
    x = Stack[i](xi).simplify()
    if ab:
        S[0], S[n] = ab

    return ym, x, i, n

def dissect_variance(variance):
    dx = variance.of(Expr ** 2)
    ym, x_mean = dx.of(Expr - Expr)

    x_sum, n = x_mean.of(Expr / Expr)
    xi, (i, *ab) = x_sum.of(Sum)
    x = Stack[i](xi).simplify()
    if ab:
        S[0], S[n] = ab

    return ym, x, i, n


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset, Finset

    n, m = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    y = Symbol(real=True)
    i = Symbol(integer=True)
    Eq << apply((y - Sum[i](x[i]) / n) ** 2)

    x_ = Symbol('x', Stack[i](y - x[i]))
    Eq << x_[i].this.definition

    Eq << Eq[-1] - y

    Eq << -Eq[-1]

    Eq << Eq[0].lhs.this.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    # Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.to.mul)
    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].subs(x_[i].this.definition)

    Eq << Eq[0].this.rhs.find(Sum).apply(Algebra.Sum.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

# created on 2019-11-02
