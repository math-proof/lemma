from util import *


@apply
def apply(self):
    expr, *limits = self.of(Stack[ReducedMin])
    return Equal(self, ReducedMin(Stack(expr, *limits).simplify()))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Stack[i:n](ReducedMin(a[i])))
    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2019-10-20
