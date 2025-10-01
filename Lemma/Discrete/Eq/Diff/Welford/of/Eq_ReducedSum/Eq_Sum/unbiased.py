from util import *


@apply
def apply(eq_x_bar, eq_s2):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    (s, S[n]), ((diff, limit), S[n]) = eq_s2.of(Equal[Indexed ** 2, Sum[Expr ** 2] / (Symbol - 1)])
    k, S[0], S[n] = limit
    S[x[k]], S[x_bar[n]] = diff.of(Expr - Expr)
    return Equal(Difference[n](s[n] ** 2), (x[n] - x_bar[n]) ** 2 / (n + 1) - s[n] ** 2 / n)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Logic

    x, s = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), Equal(s[n] ** 2, Sum[k:n]((x[k] - x_bar[n]) ** 2) / (n - 1)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[1] * (n - 1)

    Eq << Discrete.Eq.Diff.Welford.of.Eq_ReducedSum.Eq_Sum.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.doit()

    Eq << Algebra.Sub.eq.Mul.of.Eq_ReducedSum.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=0)

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Logic.Cond.of.And.apply(Eq[-1], 1).reversed

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq[-1], Eq[-3])





if __name__ == '__main__':
    run()
# created on 2023-11-06
# updated on 2023-11-07
