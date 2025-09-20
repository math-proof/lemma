from util import *


@apply
def apply(self, k):
    f, (j, S[0], n), (i, S[0], m) = self.of(Stack)

    A = Stack[i:m, j:k](f).simplify()
    B = Stack[i:m, j:n - k](f._subs(j, j + k))

    return Equal(self, BlockMatrix([A, B]).T, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n))
    f = Function(real=True)
    Eq << apply(Stack[j:n, i:m](f(i, j)), k)

    i = Symbol(domain=Range(m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.Block.split, k)



if __name__ == '__main__':
    run()
# created on 2019-10-22
# updated on 2021-11-22
