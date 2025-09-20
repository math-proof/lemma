from util import *


@apply
def apply(subset, piecewise=None):
    from sympy import Set
    args, S = subset.of(Subset[FiniteSet, Set])
    assert {e for e, _ in piecewise.args} == {*args}
    return Element(piecewise, S)


@prove
def prove(Eq):
    from Lemma import Set, Logic

    x = Symbol(integer=True, given=True)
    S, A, B = Symbol(etype=dtype.integer, given=True)
    f, g, h = Function(real=True)
    Eq << apply(Subset({f(x), g(x), h(x)}, S),
                piecewise=Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True)))

    Eq << Set.In.of.Subset.apply(Eq[0])

    Eq.bool_fx = Set.Eq.Bool.In.of.In.apply(Eq[-1])

    Eq << Set.In.of.Subset.apply(Eq[0], 1)

    Eq.bool_gx = Set.Eq.Bool.In.of.In.apply(Eq[-1])

    Eq << Set.In.of.Subset.apply(Eq[0], 2)

    Eq.bool_hx = Set.Eq.Bool.In.of.In.apply(Eq[-1])

    Eq.plausible = Or(Equal(Bool(Element(f(x), S)), 1) & Element(x, A),
                      Equal(Bool(Element(g(x), S)), 1) & Element(x, B - A),
                      Equal(Bool(Element(h(x), S)), 1) & NotElement(x, A | B), plausible=True)

    Eq << Eq.plausible.subs(Eq.bool_fx).subs(Eq.bool_gx).subs(Eq.bool_hx)

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq << Eq.plausible.this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Set.InIte__Ite.of.And.ou.OrAndS.apply(Eq[-1], wrt=S)



if __name__ == '__main__':
    run()
# created on 2020-11-03
# updated on 2023-05-14
