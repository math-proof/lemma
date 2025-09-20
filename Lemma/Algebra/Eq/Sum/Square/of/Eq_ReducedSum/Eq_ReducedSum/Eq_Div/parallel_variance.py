from util import *


@apply
def apply(eq_x_bar_A, eq_x_bar_B, eq_x_bar, k=None):
    ((x_A, (S[0], n_A)), S[n_A]), x_bar_A = eq_x_bar_A.of(Equal[ReducedSum[Sliced] / Symbol])
    ((x_B, (S[0], n_B)), S[n_B]), x_bar_B = eq_x_bar_B.of(Equal[ReducedSum[Sliced] / Symbol])
    x_bar_AB = eq_x_bar.of(Equal[(n_A * x_bar_A + n_B * x_bar_B) / (n_A + n_B)])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k')
    return Equal(
        Sum[k:n_A]((x_A[k] - x_bar_AB) ** 2) + Sum[k:n_B]((x_B[k] - x_bar_AB) ** 2),
        Sum[k:n_A]((x_A[k] - x_bar_A) ** 2) + Sum[k:n_B]((x_B[k] - x_bar_B) ** 2) + (x_bar_B - x_bar_A) ** 2 * n_A * n_B / (n_A + n_B))


@prove
def prove(Eq):
    from Lemma import Algebra

    x_A = Symbol("x^A", real=True, shape=(oo,))
    x_B = Symbol("x^B", real=True, shape=(oo,))
    n_A, n_B, k = Symbol(integer=True)
    x_bar_A = Symbol(r"{\overline {x}}_A", real=True)
    x_bar_B = Symbol(r"{\overline {x}}_B", real=True)
    x_bar_AB = Symbol(r"{\overline {x}}_{AB}", real=True)
    Eq << apply(
        Equal(x_bar_A, ReducedSum(x_A[:n_A]) / n_A),
        Equal(x_bar_B, ReducedSum(x_B[:n_B]) / n_B),
        Equal(x_bar_AB, (n_A * x_bar_A + n_B * x_bar_B) / (n_A + n_B)))

    Eq <<= (Eq[-1].lhs.find(Sum[Add ** 2]) - Eq[-1].rhs.find(Sum[Add ** 2])).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum), (Eq[-1].lhs.find(Sum[Add ** 2][2]) - Eq[-1].rhs.find(Sum[Add ** 2][2])).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq <<= Eq[-2].this.rhs.expr.apply(Algebra.Sub.Square.eq.Mul), Eq[-1].this.rhs.expr.apply(Algebra.Sub.Square.eq.Mul)

    Eq <<= Eq[-2].this.rhs.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS), Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq <<= (Eq[0] * n_A).this.rhs.apply(Algebra.ReducedSum.eq.Sum, k), (Eq[1] * n_B).this.rhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq <<= Eq[-4].subs(Eq[-2].reversed), Eq[-3].subs(Eq[-1].reversed)

    Eq <<= Eq[-2].this.find(Mul - Mul).apply(Algebra.Add.eq.Mul), Eq[-1].this.find(Mul - Mul).apply(Algebra.Add.eq.Mul)

    Eq <<= Eq[-2].this.rhs.subs(Eq[2]), Eq[-1].this.rhs.subs(Eq[2])

    Eq <<= Eq[-2].this.rhs.find((~Add) ** 2).apply(Algebra.Add.eq.Mul.together), Eq[-1].this.rhs.find((~Add) ** 2).apply(Algebra.Add.eq.Mul.together)

    Eq <<= Eq[-2].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS), Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq <<= Eq[-2].this.rhs.find((~Add) ** 2).apply(Algebra.Add.eq.Mul), Eq[-1].this.rhs.find((~Add) ** 2).apply(Algebra.Add.eq.Mul)

    Eq << Eq[-2].this.rhs.find(Add ** 2).apply(Algebra.Square.Neg)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)


    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=slice(2, None))
    # http://i.stanford.edu/pub/cstr/reports/cs/tr/79/773/CS-TR-79-773.pdf



if __name__ == '__main__':
    run()
# created on 2023-11-07
