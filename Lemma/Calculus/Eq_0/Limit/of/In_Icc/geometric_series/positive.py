from util import *


@apply
def apply(el, n):
    x, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.left_open and domain.right_open
    return Equal(Limit[n:oo](x ** n), Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Bool

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(0, 1, left_open=True, right_open=True)), n)

    Eq << Calculus.Eq_Limit.given.Any_All.limit_definition.restricted.apply(Eq[1])

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.given.Lt.Log)

    Eq.gt_zero = Set.Gt.of.In_Icc.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.EqLog.of.Gt_0.apply(Eq.gt_zero, Eq[-1].find(All).variable)

    Eq.any = Eq[-2].subs(Eq[-1])

    Eq.lt_zero = Set.Lt_0.Log.of.In_Icc.apply(Eq[0])

    Eq << Element(Eq.any.find(Mul < ~Log), Interval.open(-oo, 0), plausible=True)

    Eq << Set.In.Div.of.Lt_0.In.apply(Eq.lt_zero, Eq[-1], simplify=None)

    Eq.Ceiling_el = Set.In_Ico.Ceil.of.In_Icc.apply(Eq[-1])

    Eq << Algebra.Any.given.Cond.subst.apply(Eq.any, Eq.any.variable, Eq.Ceiling_el.lhs)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Bool.All.given.Imp.apply(Eq[-1])

    Eq << Algebra.GeCeil.apply(Eq.Ceiling_el.lhs.arg)

    Eq << Algebra.Gt.of.Ge.relax.apply(Eq[-1], step=1)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.of.Ge.Gt)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq.lt_zero, Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.LtMul.of.Lt_0.Gt)





if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-11-05
