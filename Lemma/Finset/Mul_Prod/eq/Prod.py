from util import *


@apply
def apply(self):
    from Lemma.Algebra.Add.eq.Sum.limits.unshift import absorb
    return Equal(self, absorb(Product, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(n))
    f = Function(integer=True)
    Eq << apply(Mul(Product[k:1 + i:n](f(k)), f(i)))

    Eq << Eq[-1].this.rhs.apply(Finset.Prod.eq.MulProdS, cond={i})


if __name__ == '__main__':
    run()
# created on 2018-04-15
