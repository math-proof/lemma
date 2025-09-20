from util import *


@apply
def apply(self, index=0):
    from Lemma.Algebra.Sum.limits.pop.Slice import rewrite
    return Equal(self, rewrite(Minima, self, index))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Minima[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.apply(Algebra.Minima.limits.concat)





if __name__ == '__main__':
    run()
# created on 2020-12-18
# updated on 2023-11-18
