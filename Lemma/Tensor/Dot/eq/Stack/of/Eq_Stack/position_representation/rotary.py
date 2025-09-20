from util import *


def rotary_matrix(d, b, i, j, k):
    return Stack[k:d, j:d](
        Piecewise(
            (Piecewise(
                (cos(i / b ** (j / d)), Equal(j, k)),
                (-sin(i / b ** (j / d)), Equal(j, k - 1)),
                (0, True)), Equal(j % 2, 0)),
            (Piecewise(
                (cos(i / b ** ((j - 1) / d)), Equal(j, k)),
                (sin(i / b ** ((j - 1) / d)), Equal(j, k + 1)),
                (0, True)), True)))

def extract(eq_R):
    (piece, (k, S[0], d), (j, S[0], S[d])), Ri = eq_R.of(Equal[Stack])
    (((even_expr, (S[j], S[k])), (S[even_expr], (S[j], S[k - 1]))), S[j]), ((odd_expr, (S[j], S[k])), (S[odd_expr], (S[j], S[k + 1]))) = piece.of(
        Piecewise[
            ExprCondPair[
                Piecewise[
                    ExprCondPair[Cos, Equal],
                    ExprCondPair[-Sin, Equal],
                    ExprCondPair[0, S.true]
                ],
                Equal[Expr % 2, 0]],
            ExprCondPair[
                Piecewise[
                    ExprCondPair[Cos, Equal],
                    ExprCondPair[Sin, Equal],
                    ExprCondPair[0, S.true]
                ],
                S.true]
        ])

    i, (b, (S[j], S[d])) = even_expr.of(Expr * Expr ** (-Expr / Expr))
    S[i / b ** ((j - 1) / d)] = odd_expr
    return (Ri, d), b, (i, j, k)


@apply
def apply(eq_R, x):
    (Ri, d), b, (i, j, k) = extract(eq_R)
    return Equal(
        Ri @ x,
        Stack[j:d](
            Piecewise(
                (x[j] * cos(i / b ** (j / d)) - x[j + 1] * sin(i / b ** (j / d)), Equal(j % 2, 0)),
                (x[j] * cos(i / b ** ((j - 1) / d)) + x[j - 1] * sin(i / b ** ((j - 1) / d)), True))))




@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # x_i denotes token embedding at index i (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    # i denotes token index
    # j denotes row index
    # k denotes column index
    i, j, k = Symbol(integer=True)
    Eq << apply(Equal(R(i), rotary_matrix(d, b, i, j, k)), x[i])

    Eq << Eq[0] @ x[i]

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Stack)().find(Element).simplify()

    Eq << Eq[-1].this.find(Stack)().find(Element[Symbol, Range[0]]).simplify()

    Eq << Eq[-1].this.rhs().expr.args[0]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().find(Element).simplify()

    Eq << Eq[1].this.rhs.expr.apply(Algebra.Ite.eq.Add.Ite, [-1, slice(1, None)])

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Ite.eq.Mul)

    # reference:
    # https://arxiv.org/pdf/2104.09864.pdf#page=7




if __name__ == '__main__':
    run()
# created on 2023-05-22
# updated on 2023-09-16
