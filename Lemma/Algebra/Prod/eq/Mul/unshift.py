from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Sub.unshift import rewrite
    def inverse(x):
        assert x.is_nonzero
        return 1 / x
    return Equal(self, rewrite(Product, self, inverse), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    C = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True, positive=True)
    Eq << apply(Product[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(Algebra.Prod.eq.MulProdS, cond={0})




if __name__ == '__main__':
    run()

# created on 2020-03-10
# updated on 2023-03-30
