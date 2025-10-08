from util import *


@apply
def apply(given, wrt=None):
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return Supset(Piecewise(*expr_cond_pair(Supset, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, S = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(etype=dtype.real[k])
    Eq << apply(Supset(f(x), S) & Element(x, A) | Supset(g(x), S) & Element(x, B - A) | Supset(h(x), S) & NotElement(x, A | B), wrt=S)

    Eq << Eq[0].this.find(Element[Complement]).apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Eq[-1].apply(Bool.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Set.Supset.Ite.of.Or.two, wrt=S)

    Eq << Eq[-1].apply(Set.Supset.Ite.of.Or.two, wrt=S)




if __name__ == '__main__':
    run()

# created on 2021-06-15
# updated on 2023-05-14

from . import two
