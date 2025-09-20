from util import *


@apply
def apply(is_positive):
    limit, R = is_positive.of(Element)
    (fx, *limits) = limit.of(Limit)
    assert R in Interval.open(0, oo)
    return Equal(Limit(abs(fx), *limits), limit)


@prove
def prove(Eq):
    from Lemma import Set, Calculus, Algebra, Logic

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Interval.open(0, oo)))

    Eq << Set.Eq.of.In.definition.apply(Eq[0], 'y')

    y = Eq[-1].lhs
    δ_0 = Symbol(positive=True)
    Eq <<= Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[-1], delta=δ_0), Eq[1].subs(Eq[-1].reversed)

    δ = Symbol(positive=True)
    Eq << Calculus.Eq_Limit.given.Any_All.limit_definition.apply(Eq[-1], delta=δ)

    Eq << Greater(y, 0, plausible=True)

    δ_1 = Symbol(positive=True)
    Eq << Calculus.Any.All.Gt.of.Gt_0.Eq_Limit.apply(Eq[-1], Eq[2], delta=δ_1)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt.of.Gt.relax, 0)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq[-1], Eq[3])

    Eq << Eq[-1].this.find(Less & Less).args[:2].apply(Algebra.Lt.Lt.given.Lt.Min)

    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.EqAbs.of.Gt)

    Eq << Eq[-1].this.find(And).apply(Logic.Cond.of.Eq.Cond.subst, reverse=True)


if __name__ == '__main__':
    run()
# created on 2023-04-18
