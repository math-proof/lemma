from util import *


@apply
def apply(given, wrt=None):
    from Lemma.Logic.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Element(wrt, Piecewise(*expr_cond_pair(Element, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(etype=dtype.real[k])
    Eq << apply(Element(y, f(x)) & Element(x, A) | Element(y, g(x)) & Element(x, B - A) | Element(y, h(x)) & NotElement(x, A | B), wrt=y)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Eq[-1].apply(Logic.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Set.In.Ite.of.Or.rhs.two, wrt=y)

    Eq << Eq[-1].apply(Set.In.Ite.of.Or.rhs.two, wrt=y)


if __name__ == '__main__':
    run()

# created on 2018-09-24
# updated on 2023-05-14

from . import two
