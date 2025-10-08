from util import *


@apply
def apply(eq_x_bar, eq_M2):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    (diff, limit), Mn2 = eq_M2.of(Equal[Sum[Expr ** 2]])
    k, S[0], S[n] = limit
    S[x[k]], S[x_bar[n]] = diff.of(Expr - Expr)
    return Equal(Difference[n](Mn2), (x[n] - x_bar[n + 1]) * (x[n] - x_bar[n]))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, M = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), Equal(M[n] ** 2, Sum[k:n]((x[k] - x_bar[n]) ** 2)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[1].subs(n, n + 1) - Eq[1]

    Eq << Eq[-1].this(n).find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Algebra.Eq.Sum.Square.eq.Add.Sum.Square.of.Eq_ReducedSum.apply(Eq[0], x_bar[n + 1], k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Eq.Add.Square.eq.Mul.of.Eq_ReducedSum.apply(Eq[0])

    Eq << Bool.Eq.of.Eq.Eq.apply(*Eq[-2:])




if __name__ == '__main__':
    run()
# created on 2023-11-07

from . import unbiased
from . import biased
