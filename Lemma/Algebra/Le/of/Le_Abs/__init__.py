from util import *


@apply
def apply(given):
    from Lemma.Algebra.Abs.Sum.eq.Mul.Sum import dissect_distance
    dx, dy = given.of(LessEqual)

    yt, x, i, n = dissect_distance(dx)

    S[yt], y_mean = dy.of(Abs[Expr - Expr])

    y_sum, m = y_mean.of(Expr / Expr)

    yj, (j, *ab) = y_sum.of(Sum)
    if ab:
        S[0], S[m] = ab

    y, S[j] = yj.of(Indexed)
    S[y], t = yt.of(Indexed)
    assert t < m

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2) + (yt - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2 + Sum[j:m]((y[j] - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2) - (yt - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2,
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    m = Symbol(domain=Range(2, oo))
    y = Symbol(real=True, shape=(m,))
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(m))
    Eq << apply(abs(y[t] - Sum[i](x[i]) / n) <= abs(y[t] - Sum[j](y[j]) / m))

    Eq << Eq[-1].rhs.args[0].this.apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].find(Sum, Sum).this.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(x[n], y[t])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.Square.eq.Div.Sum.Square)

    Eq << Eq[-1].this.rhs.args[0].find(Sum).limits_subs(i, j)

    Eq << Algebra.LeAddSDivS.of.LeAbsSSub_DivSum.apply(Eq[0])

    Eq << Eq[-1].this.lhs.args[1].find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.DivSubS.eq.SubSum_SquareSub_DivSubSum)

    Eq << Eq[-1].this.lhs.find(Add, Mul, Add, Sum).limits_subs(i, j, simplify=None)

    Eq << Eq[-1].this.lhs.find(Sum, Add, Mul, Add, Sum).limits_subs(i, j, simplify=None)

    Eq << Eq[-1].this.lhs.args[2].limits_subs(i, j, simplify=None)

    Eq << Eq[-1].this.lhs.args[0].find(Expr ** 2).apply(Algebra.Square.Neg)





if __name__ == '__main__':
    run()


# created on 2019-11-28
# updated on 2023-05-06


from . import function
