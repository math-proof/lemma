from util import *


@apply
def apply(self):
    base, exp = self.of(Pow)
    fn, *limits = base.of(Product)
    assert exp >= 0 or exp.is_integer
    return Equal(self, Product(fn ** exp, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    f = Function(real=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, given=False, positive=True)
    t = Symbol(integer=True, nonnegative=True)

    Eq << apply(Product[k:n](f(k)) ** t)

    Eq << Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.apply(Algebra.Prod.eq.MulProdS, cond={n})

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.MulProdS, cond={n})

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[0] * Eq[-1].find(Pow)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-01-31
