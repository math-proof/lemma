from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Finset.SumIco.eq.Sum_UFnAdd import limits_subs
    return Equal(self, limits_subs(Product, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Bool, Finset

    n, d = Symbol(integer=True)
    f = Function(real=True)
    m = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Product[n:m](f(n)), d)

    Eq << Eq[0].subs(m, 0)

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.lhs.apply(Finset.Prod.eq.MulProdS, cond={m})

    Eq << Eq[-1].this.rhs.apply(Finset.Prod.eq.MulProdS, cond={m - d})

    Eq << Eq[0] * f(m)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Imp.of.All_Imp.apply(Eq[-1], n=m, start=0)


if __name__ == '__main__':
    run()
# created on 2020-02-26
