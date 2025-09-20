from util import *


@apply
def apply(eq_ab, eq_cd):
    (A, B), X = eq_ab.of(Equal[MatMul])
    (C, D), Y = eq_cd.of(Equal[MatMul])

    return Equal(S[
        [                                 A, Zeros(A.shape[0], C.shape[1])],
        [Zeros(C.shape[0], A.shape[1]),                                  C]] @ [
        [                                 B, Zeros(B.shape[0], D.shape[1])],
        [Zeros(D.shape[0], B.shape[1]),                                  D]], [
        [                                 X, Zeros(X.shape[0], Y.shape[1])],
        [Zeros(Y.shape[0], X.shape[1]),                                  Y]])


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D, X, Y = Symbol(shape=(n, n), real=True)
    Eq << apply(Equal(A @ B, X), Equal(C @ D, Y))

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(*Eq[:2])


if __name__ == '__main__':
    run()
# created on 2023-09-16
