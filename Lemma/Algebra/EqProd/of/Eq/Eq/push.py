from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.push import absorb_back
    return absorb_back(Product, Equal, *imply)


@prove
def prove(Eq):
    from Lemma import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)
    Eq << apply(Equal(g(b), f(b)), Equal(Product[k:a:b](g(k)), Product[k:a:b](f(k))))

    Eq << Algebra.EqMul.of.Eq.Eq.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Prod.eq.MulProdS, cond={b})

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.MulProdS, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-03-25
