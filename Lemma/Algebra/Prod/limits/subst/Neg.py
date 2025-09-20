from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.Sum.limits.subst.Neg import limits_subs
    return Equal(self, limits_subs(Product, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Product[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.Neg.Infty)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.subst.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.In_Icc.Is.InAdd, c)

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Prod_Pow_Bool)


if __name__ == '__main__':
    run()
# created on 2020-02-27
