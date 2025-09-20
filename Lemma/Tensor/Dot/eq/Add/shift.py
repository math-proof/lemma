from util import *


@apply
def apply(self):
    a, b = self.of(MatMul)
    n = a.shape[0]
    i = self.generate_var(integer=True)
    a0 = a[0]
    b0 = b[0]
    a = Stack[i:1:n](a[i]).simplify()
    b = Stack[i:1:n](b[i]).simplify()

    return Equal(self, a @ b + a0 * b0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    i, k, j = Symbol(integer=True)
    L, H = Symbol(real=True, shape=(oo, oo))
    Eq << apply(L[i, :k] @ H[j, :k])

    Eq << Eq[0].this.lhs.args[0].apply(Algebra.Expr.eq.Block, 1)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Expr.eq.Block, 1)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Block)




if __name__ == '__main__':
    run()
# created on 2023-06-24
