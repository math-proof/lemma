from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[
        BlockMatrix[
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones,
                    Sliced[Indexed]
                ],
            ],
            Stack[Tuple[Expr - Expr]]
        ] - Stack[Ones * logsumexp]])

    (S[A], (([S[l - 1]], [S[0]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[Ones] - 1]]]])

    assert n >= 2 and l >= 2 and l <= n

    (h, i), (S[i], S[l - 1]) = el.of(Element[Indexed, Range[-Min, 1]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i] + l - 1])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    z_quote = Symbol(shape=(n, l), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l](A[i + l, i + 1:i + l + 1])) - Stack[i:n](Ones(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))),
        Element(h[i], Range(-Min(i, l - 1), 1)))

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.lower_triangle.apply(Eq[1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_relu, Eq.lt_1 = Set.And.of.In_Range.apply(Eq[2])

    Eq << Eq.ge_relu.this.find(Min).args[0].apply(Algebra.Expr.eq.Ite, upper=n - 1)

    Eq << Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq << -Eq[-1]

    Eq.ge = -Algebra.Le.of.Le.relax.apply(Eq[-1], upper=Min(l - 1, n - 1))



    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.ge, Eq.eq, invert=True)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.lt_1, Eq[-1])

    Eq << Algebra.EqLog.of.Eq.apply(Eq[-1])

    Eq.loss = -Algebra.EqSumS.of.Eq.apply(Eq[3] * (1 + log(1 - h[i] / 2)), (i, 0, n))





if __name__ == '__main__':
    run()
# created on 2022-01-05

# updated on 2022-03-30


from . import tf
