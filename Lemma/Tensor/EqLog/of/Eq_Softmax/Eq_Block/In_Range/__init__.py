from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u)]), (S[i + n - Min(n, u)], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones,
                    Sliced[Indexed]
                ],
                Tuple[Min]
                ],
            Stack
            ],
        BlockMatrix[
            Stack[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones
                    ],
                Tuple[Min]
                ]
            ]
        ] - Stack[Ones * logsumexp]])

    assert n >= 2 and u >= 2 and l >= 2

    (S[A], (([S[l - 1]], [S[u - 1]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[Ones] - 1]]]])

    (h, S[i]), ((S[i], S[l - 1]), (S[u], S[n - i])) = el.of(Element[Indexed, Range[-Min, Min]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i] + Min(l, n) - 1])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    n, l, u = Symbol(domain=Range(2, oo))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z_quote = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix[1](
            BlockMatrix(
                Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i, :i])),
                Stack[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])),
            BlockMatrix(
                Stack[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
                Stack[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * Ones(i))))) - Stack[i:n](Ones(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))),
        Element(h[i], Range(-Min(i, l - 1), Min(n - i, u))))

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_Sub_Stack_Mul_LogSumExp.apply(Eq[1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_neg_min, Eq.lt_min = Set.And.of.In_Ico.apply(Eq[2])

    Eq <<= Eq.ge_neg_min.this.find(Min).args[0].apply(Algebra.Expr.eq.IteGe, upper=n - 1), Eq.lt_min.this.find(Add).apply(Algebra.Expr.eq.IteGe, upper=n)

    Eq <<= -Eq[-2].this(i).find(GreaterEqual).simplify(), Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq.lt = Algebra.Lt.of.Lt.relax.apply(Eq[-1], upper=Min(n, u))

    Eq << Algebra.Le.of.Le.relax.apply(Eq[-2], upper=Min(l - 1, n - 1))

    Eq.ge = -Eq[-1].this.rhs.apply(Algebra.Min.eq.Add)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.ge, Eq.eq, invert=True)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.lt, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)

    Eq << Algebra.EqLog.of.Eq.apply(Eq[-1])

    Eq.loss = -Algebra.EqSumS.of.Eq.apply(Eq[3] * (1 + log(1 + abs(h[i]) / 2)), (i, 0, n))




if __name__ == '__main__':
    run()
# created on 2022-01-05


# updated on 2023-05-19
from . import upper_triangle
from . import lower_triangle
from . import tf
