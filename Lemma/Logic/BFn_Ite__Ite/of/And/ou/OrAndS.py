from util import *


@apply
def apply(given, wrt=None, reverse=True):
    from Lemma.Logic.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Equal(Piecewise(*expr_cond_pair(Equal, or_eqs, wrt, reverse=reverse)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, f(x)) & Element(x, A) | Equal(p, g(x)) & Element(x, B - A) | Equal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Eq[-1].apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Logic.BFn_Ite.of.OrAndS, wrt=p)

    Eq << Eq[-1].apply(Logic.BFn_Ite.of.OrAndS, wrt=p)

    Eq << Eq[-1].reversed







if __name__ == '__main__':
    run()

# created on 2018-01-17
# updated on 2023-05-14
