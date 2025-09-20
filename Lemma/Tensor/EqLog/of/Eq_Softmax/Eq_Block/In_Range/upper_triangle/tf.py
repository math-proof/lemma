from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[
        BlockMatrix[
            Stack[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones],
                Tuple[Min - 1]]] - Stack[Ones * logsumexp]])

    (S[A], (([S[0]], [S[u - 1]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[Ones] - 1]]]])

    assert n >= 2 and u >= 2

    (h, S[i]), (S[0], (S[u], S[n - i])) = el.of(Element[Indexed, Range[Min]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i]])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    n, u = Symbol(domain=Range(2, oo))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    z_quote = Symbol(shape=(n, Min(u, n)), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix(
            Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1)))) - Stack[i:n](Ones(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))),
        Element(h[i], Range(Min(n - i, u))))

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.upper_triangle.tf.apply(Eq[1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_zero, Eq.lt_min = Set.And.of.In_Range.apply(Eq[2])

    Eq << Eq.lt_min.this.find(Add).apply(Algebra.Expr.eq.IteGe, upper=n)

    Eq << Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq.lt = Algebra.Lt.of.Lt.relax.apply(Eq[-1], upper=Min(n, u))

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.lt, Eq.eq)

    Eq << Eq[-1].this.find(Less) - i

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.ge_zero, Eq[-1], invert=True)

    Eq << Algebra.EqLog.of.Eq.apply(Eq[-1])

    Eq.loss = -Algebra.EqSumS.of.Eq.apply(Eq[3] * (1 + log(1 + h[i] / 2)), (i, 0, n))





if __name__ == '__main__':
    run()
# created on 2022-01-05
# updated on 2023-05-20
