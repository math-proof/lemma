from util import *


@apply
def apply(x):
    n = x.shape[0]
    i, j = Symbol(domain=Range(n))

    w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))

    return Equal(x @ w[i, j] @ w[i, j], x)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Int

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    Eq << (x @ w[i, j]).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << (Eq[-1] @ w[i, j]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Piecewise).apply(Int.Ite.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    k = Eq[-1].rhs.variable
    Eq << Eq[-1].this.find(Add).expand()

    Eq << Eq[-1].this.find(Stack[~Add]).apply(Algebra.Add.collect, factor=KroneckerDelta(j, k))

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.Delta.eq.Zero)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-15
# updated on 2022-10-11
