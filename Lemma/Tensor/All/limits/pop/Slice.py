from util import *


@apply
def apply(self, index=0):
    from Lemma.Tensor.Sum.limits.pop.Slice import rewrite
    return rewrite(All, self, index)


@prove
def prove(Eq):
    from Lemma import Tensor

    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, bool=True)
    Eq << apply(All[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.apply(Tensor.All.limits.concat)





if __name__ == '__main__':
    run()
# created on 2023-07-02
# updated on 2023-11-18
