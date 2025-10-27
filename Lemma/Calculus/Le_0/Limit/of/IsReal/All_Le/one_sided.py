from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    x0, epsilon = x0.clear_infinitesimal()
    assert epsilon
    assert R in Reals
    S[fx], (x, *cond) = all_le.of(All[Expr <= 0])
    if epsilon > 0:
        S[x0], delta = cond
        delta -= x0
        assert delta > 0
    else:
        delta, S[x0] = cond
        delta -= x0
        assert delta < 0

    return lim <= 0


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Bool, Set, Nat

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals),
        All[x:x0:x0 + delta](f(x) <= 0))

    Eq << ~Eq[2]

    A = Symbol(Eq[-1].lhs)
    Eq << A.this.definition.reversed

    Eq << Eq[-2].subs(Eq[-1])

    δ_quote = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.Gt.of.Gt_0.Eq_Limit.apply(*Eq[-2:], delta=δ_quote)

    Eq << Algebra.Any.All.And.of.Cond.Any_All.apply(Eq[-2] / 2, Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Nat.Gt.of.Gt.Gt)

    Eq << Eq[-1].this.find(All).apply(Set.AllIn_SDiff.of.All, domain=Interval.open(x0, x0 + Min(δ_quote, delta)))

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[1], domain=Interval.open(x0, x0 + Min(δ_quote, delta)))

    Eq << Bool.Any_And.of.Any.All.apply(*Eq[-2:], simplify=None)






if __name__ == '__main__':
    run()
# created on 2023-10-15
