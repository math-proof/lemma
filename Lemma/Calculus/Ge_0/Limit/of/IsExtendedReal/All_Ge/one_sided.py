from util import *


@apply
def apply(el, all_ge):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    x0, epsilon = x0.clear_infinitesimal()
    assert epsilon
    assert R in ExtendedReals
    S[fx], (x, *ab) = all_ge.of(All[Expr >= 0])
    if epsilon > 0:
        S[x0], delta = ab
        delta -= x0
        assert delta > 0
    else:
        delta, S[x0] = ab
        delta -= x0
        assert delta < 0
    return lim >= 0


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Set, Logic

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 - S.Infinitesimal](f(x)), ExtendedReals),
        All[x:x0 - delta:x0](f(x) >= 0))

    Eq.is_real, Eq.is_not_real = Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Element(Limit[x:x0 - S.Infinitesimal](f(x)), Reals))

    Eq << Logic.Imp.given.And.Imp.invert.apply(Eq.is_real, cond=Eq[1])

    Eq << Logic.Or.given.Cond.apply(Eq[-1], -1)

    Eq << Eq[-2].this.lhs.apply(Calculus.Ge_0.Limit.of.IsReal.All_Ge.one_sided)

    Eq.infer, Eq.le_infinity = Logic.Imp.given.And.Imp.invert.apply(Eq.is_not_real, cond=Eq[0])

    Eq << Eq[0].simplify()

    Eq.ne_infinity = Unequal(Limit[x:x0 - S.Infinitesimal](f(x)), -oo, plausible=True)

    Eq << ~Eq.ne_infinity

    δ_quote = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.Lt_0.of.Eq_Infty.apply(Eq[-1], delta=δ_quote)

    Eq << Eq[-1].this.expr.apply(Set.AllIn_SDiff.of.All, domain=Interval.open(x0 - Min(delta, δ_quote), x0))

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[1], domain=Interval.open(x0 - Min(delta, δ_quote), x0))

    Eq << Logic.Any_And.of.Any.All.apply(*Eq[-2:])

    Eq << Logic.Imp.given.And.Imp.invert.apply(Eq.infer, cond=Eq.ne_infinity)

    Eq << Eq[-1].this.lhs.apply(Set.In_SDiff.of.In.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge_0.of.Eq)




if __name__ == '__main__':
    run()
# created on 2023-10-15
