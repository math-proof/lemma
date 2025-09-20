from util import *


@apply
def apply(eq_x_bar_A, eq_x_bar_B, eq_x_delta, eq_x_bar, k=None):
    ((x_A, (S[0], n_A)), S[n_A]), x_bar_A = eq_x_bar_A.of(Equal[ReducedSum[Sliced] / Symbol])
    ((x_B, (S[0], n_B)), S[n_B]), x_bar_B = eq_x_bar_B.of(Equal[ReducedSum[Sliced] / Symbol])
    δ = eq_x_delta.of(Equal[x_bar_B - x_bar_A])
    x_bar_AB = eq_x_bar.of(Equal[x_bar_A + δ * n_B / (n_A + n_B)])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k')
    return Equal(
        Sum[k:n_A]((x_A[k] - x_bar_AB) ** 2) + Sum[k:n_B]((x_B[k] - x_bar_AB) ** 2),
        Sum[k:n_A]((x_A[k] - x_bar_A) ** 2) + Sum[k:n_B]((x_B[k] - x_bar_B) ** 2) + δ ** 2 * n_A * n_B / (n_A + n_B))


@prove
def prove(Eq):
    from Lemma import Algebra

    x_A = Symbol("x^A", real=True, shape=(oo,))
    x_B = Symbol("x^B", real=True, shape=(oo,))
    n_A, n_B, k, δ = Symbol(integer=True)
    x_bar_A = Symbol(r"{\overline {x}}_A", real=True)
    x_bar_B = Symbol(r"{\overline {x}}_B", real=True)
    x_bar_AB = Symbol(r"{\overline {x}}_{AB}", real=True)
    Eq << apply(
        Equal(x_bar_A, ReducedSum(x_A[:n_A]) / n_A),
        Equal(x_bar_B, ReducedSum(x_B[:n_B]) / n_B),
        Equal(δ, x_bar_B - x_bar_A),
        Equal(x_bar_AB, x_bar_A + δ * n_B / (n_A + n_B)))

    Eq << Eq[3].subs(Eq[2])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.find(~Mul + Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Algebra.Eq.Sum.Square.of.Eq_ReducedSum.Eq_ReducedSum.Eq_Div.parallel_variance.apply(*Eq[:2], Eq[-1], k)

    Eq << Eq[-1].subs(Eq[2].reversed)
    # https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance# Parallel_algorithm



if __name__ == '__main__':
    run()
# created on 2023-11-08
