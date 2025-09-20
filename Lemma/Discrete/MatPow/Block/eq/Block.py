from util import *


@apply
def apply(self):
    X = self.of(MatPow[Expr, 2])
    from Lemma.Tensor.Dot.eq.Block import matmul
    return Equal(self, matmul(X, X, deep=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D, E, F, G, H, I = Symbol(real=True, shape=(n, n))
    Eq << apply(S[
        [A, B, C],
        [D, E, F],
        [G, H, I]] ^ 2)

    W = Symbol(Eq[0].lhs.find(BlockMatrix))
    Eq << W.this.definition

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.Block, n, n)

    Eq << W[:n, n:].this.apply(Algebra.Expr.eq.Block, n, axis=1)

    Eq << W[n:, :n].this.apply(Algebra.Expr.eq.Block, n)

    Eq << W[n:, n:].this.apply(Algebra.Expr.eq.Block, n, n)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq << Eq[-1] @ Eq[1].rhs

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()
# created on 2023-09-16
