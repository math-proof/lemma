from util import *


@apply
def apply(self, pivot=-1):
    a, b = std.array_split(self.of(MatMul), pivot)
    a = MatMul(*a)
    b = MatMul(*b)

    n = a.shape[0]
    i = self.generate_var(integer=True)

    a = Stack[i:n + 1](a[i]).simplify()
    b = Stack[i:n + 1](b[i]).simplify()

    return Equal(self, a @ b - a[n] * b[n], evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    i, k, j = Symbol(integer=True)
    L, H = Symbol(real=True, shape=(oo, oo))
    Eq << apply(L[i, :k] @ H[j, :k])

    Eq << Eq[0].this.rhs.find(MatMul).args[0].apply(Algebra.Expr.eq.Block, k)

    Eq << Eq[-1].this.rhs.find(MatMul).args[1].apply(Algebra.Expr.eq.Block, k)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)




if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-25
