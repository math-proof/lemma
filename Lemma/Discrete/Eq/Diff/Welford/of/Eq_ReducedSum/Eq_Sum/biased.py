from util import *


@apply
def apply(eq_x_bar, eq_σ2):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    (σ, S[n]), ((diff, limit), S[n]) = eq_σ2.of(Equal[Indexed ** 2, Sum[Expr ** 2] / Symbol])
    k, S[0], S[n] = limit
    S[x[k]], S[x_bar[n]] = diff.of(Expr - Expr)
    return Equal(Difference[n](σ[n] ** 2), ((x[n] - x_bar[n + 1]) * (x[n] - x_bar[n]) - σ[n] ** 2) / (n + 1))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Nat, Nat, Rat

    x, σ = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), Equal(σ[n] ** 2, Sum[k:n]((x[k] - x_bar[n]) ** 2) / n))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[1] * n

    Eq << Discrete.Eq.Diff.Welford.of.Eq_ReducedSum.Eq_Sum.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1] - Eq[1].lhs

    Eq << Eq[-1].this.lhs.args[:3:2].apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.lhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Bool.Cond.of.And.apply(Eq[-1], 1).reversed + 1

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[-1], lower=0)

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq[-1], Eq[-4])


    Eq << Eq[-1].this.rhs.apply(Nat.AddMulS.eq.Mul_Add)


if __name__ == '__main__':
    run()
# created on 2023-11-06
# updated on 2023-11-07
