from util import *


@apply
def apply(given):
    from Lemma.Algebra.Abs.Sum.eq.Mul.Sum import dissect_distance

    dx, dy = given.of(LessEqual)

    ym, x, i, n = dissect_distance(dx)

    S[ym], y_mean = dy.of(Abs[Expr - Expr])

    y_sum, m1 = y_mean.of(Expr / Expr)
    m = m1 - 1
    yj, (j, *ab) = y_sum.of(Sum)
    if ab:
        S[0], S[m1] = ab

    y = Stack[j](yj).simplify()

    assert y[m] == ym

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2) + (ym - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2 + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2),
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m + 1]((y[j] - Sum[j:m + 1](y[j]) / (m + 1)) ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    m = Symbol(domain=Range(2, oo))
    y = Symbol(real=True, shape=(m,))
    i, j = Symbol(integer=True)
    Eq << apply(abs(y[m - 1] - Sum[i](x[i]) / n) <= abs((y[m - 1] - Sum[j](y[j]) / m)))

    Eq << Eq[-1].rhs.args[0].this.apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].find(Sum, Sum).this.apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(x[n], y[m - 1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Algebra.LeAddSDivS.of.LeAbsSSubIndexed_Sub_1DivSum.apply(Eq[0])

    Eq << Eq[-1].this.lhs.find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[1].find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[0].find(Sum).expr.apply(Algebra.Square.Neg)

    Eq << Eq[-1].this.rhs.args[0].find(Sum).limits_subs(i, j)




if __name__ == '__main__':
    run()

# created on 2019-11-16
# updated on 2023-05-20
