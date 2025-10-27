from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from Lemma.Finset.Sum.eq.AddSumS import split
    return Equal(self, split(Product, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Finset

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Product[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Product).apply(Finset.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.rhs.find(Product).apply(Finset.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.find(Product[2]).apply(Finset.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.rhs.apply(Finset.MulProdS.eq.Prod_Mul)

    Eq << Eq[-1].this.rhs.expr.powsimp()

    Eq << Eq[-1].this.find(Element).apply(Set.In.Is.In_Inter.ou.In_SDiff, B)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.BoolOr.eq.SubAddBoolS)




if __name__ == '__main__':
    run()

# created on 2018-04-15
# updated on 2023-05-12
