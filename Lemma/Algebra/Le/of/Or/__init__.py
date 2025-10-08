from util import *


@apply
def apply(given, wrt=None):
    from Lemma.Bool.BFnIte.of.OrAndS import expr_cond_pair
    or_eqs = given.of(Or)

    return LessEqual(Piecewise(*expr_cond_pair(LessEqual, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    x = Symbol(real=True, given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(real=True)
    p = Symbol(real=True, given=True)
    Eq << apply(LessEqual(f(x), p) & Element(x, A) | LessEqual(g(x), p) & Element(x, B - A) | LessEqual(h(x), p) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Eq[-1].this.find(NotElement[Union]).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Eq[-1].apply(Bool.OrAndOr.of.OrAnd__OrAnd, cond=NotElement(x, A))

    Eq << Eq[-1].this.find(Or).apply(Algebra.Le.of.Or.two, wrt=p)

    Eq << Eq[-1].apply(Algebra.Le.of.Or.two, wrt=p)





if __name__ == '__main__':
    run()

# created on 2018-06-26
# updated on 2023-05-12

from . import two
