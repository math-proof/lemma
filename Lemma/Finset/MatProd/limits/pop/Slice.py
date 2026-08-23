from util import *


@apply
def apply(self, index=0):
    from Lemma.Tensor.Sum.limits.pop.Slice import rewrite
    return Equal(self, rewrite(MatProduct, self, index))


@prove
def prove(Eq):
    from Lemma import Finset

    n, m = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProduct[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.apply(Finset.MatProd.limits.concat)


if __name__ == '__main__':
    run()
# created on 2023-11-18
