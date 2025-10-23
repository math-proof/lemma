from util import *


@apply
def apply(self):
    from Lemma.Algebra.Add.eq.Sum.limits.Union import limits_union
    (function, *limits_a), (S[function], *limits_b) = self.of(Product * Product)
    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Product(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Mul(Product[k:A - B](f(k)), Product[k:A & B](f(k))))

    Eq << Eq[0].this.find(Product).apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.lhs.find(Product).apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.find(Product[2]).apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.lhs.apply(Finset.MulProdS.eq.Prod_Mul)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.find(Add).apply(Algebra.Add.principle.inclusive_exclusive)





if __name__ == '__main__':
    run()
# created on 2020-02-02
# updated on 2023-05-14
