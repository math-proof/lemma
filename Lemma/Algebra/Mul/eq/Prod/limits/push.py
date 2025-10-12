from util import *


@apply
def apply(self):
    from Lemma.Algebra.Add.eq.Sum.limits.push import absorb
    return Equal(self, absorb(Product, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset
    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(n + 1))
    f = Function(integer=True)
    Eq << apply(Mul(Product[k:i:n](f(k)), f(n)))

    Eq << Eq[-1].this.rhs.apply(Finset.Prod.eq.MulProdS, cond={n})

    # Eq << Eq[-1].this.rhs.args[0].apply(Algebra.product.to.Mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.product.to.Mul.doit.setlimit)

    # Eq << Eq[-1].this.rhs.args[0].apply(Algebra.product.to.Mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.product.to.Mul.doit.setlimit)


if __name__ == '__main__':
    run()
# created on 2020-02-01
