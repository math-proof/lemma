from util import *


@apply
def apply(self, pivot):
    expr, *limits, (i, S[0], n) = self.of(Stack)
    assert n > pivot > 0
    first = Stack(expr, *limits, (i, 0, pivot)).simplify()
    second = Stack(expr, *limits, (i, pivot, n)).simplify()
    return Equal(self, BlockMatrix([first, second]))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(positive=True, integer=True, given=False)
    m = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Stack[j:n, i:m](f(i, j)), 1)

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ite.eq.AddMulS)





if __name__ == '__main__':
    run()
# created on 2021-10-04
