from util import *


@apply
def apply(A):
    n = A.shape[0]
    k = Symbol(integer=True)
    return Equal(det(Sum[k:1:n]((ShiftMatrix(n, 0, n - 1) ^ k) @ A)), det(A) * (n - 1) * (-1) ** (n - 1))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = 6
    A = Symbol(shape=(n, n), complex=True)
    Eq << apply(A)

    L = Symbol(Eq[0].lhs.arg)
    Eq << L.this.definition

    shift = Eq[-1].rhs.expr.args[0].base
    Eq.L_definition = Eq[-1].this.rhs.doit()

    Eq << (shift @ A).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs().find(ExprCondPair[2])().expr.find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(ExprCondPair[3]).cond.simplify()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], shift)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], shift)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], shift)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], shift)

    Eq << Eq[-1] + Eq[-2] + Eq[-3] + Eq[-4] + Eq[-5]

    Eq << Eq.L_definition.subs(Eq[-1])

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 1, 0))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 2, 0))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 3, 0))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 4, 0))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 5, 0))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 0, S.One / (n - 1)))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 0, 1, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 1, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 0, 2, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 2, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 0, 3, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 3, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 0, 4, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 4, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 0, 5, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], MulMatrix(n, 5, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 1, 0, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 2, 0, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 3, 0, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 4, 0, -1))

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], AddMatrix(n, 5, 0, -1))

    Eq << Eq[-1].apply(Discrete.EqDet.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1] * (n - 1)

    Eq << -Eq[-1].subs(Eq[1])





if __name__ == '__main__':
    run()
# created on 2020-10-03
# updated on 2023-05-02
