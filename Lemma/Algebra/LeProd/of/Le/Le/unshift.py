from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.unshift import absorb_front
    return absorb_front(Product, LessEqual, *imply, criteria=lambda cond: cond.lhs >= 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True, nonnegative=True)
    f = Function(integer=True)
    Eq << apply((g(a - 1) <= f(a - 1)), Product[k:a:b](g(k)) <= Product[k:a:b](f(k)))

    Eq << Algebra.LeMul.of.Le.Le.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Prod.eq.MulProdS, cond={a - 1})

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.MulProdS, cond={a - 1})


if __name__ == '__main__':
    run()

# created on 2019-11-21
