from util import *


@apply
def apply(given, wrt=None):
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Element(Piecewise(*expr_cond_pair(Element, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, S = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Element(f(x), S) & Element(x, A) | Element(g(x), S) & Element(x, B - A) | Element(h(x), S) & NotElement(x, A | B), wrt=S)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Eq[-1].apply(Bool.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Bool.BFnIte.of.OrAndS, wrt=S)

    Eq << Eq[-1].apply(Bool.BFnIte.of.OrAndS, wrt=S)





if __name__ == '__main__':
    run()


# created on 2018-03-07
# updated on 2023-05-14

