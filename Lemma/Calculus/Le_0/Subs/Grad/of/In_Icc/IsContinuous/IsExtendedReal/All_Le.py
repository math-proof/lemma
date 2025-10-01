from util import *


@apply
def apply(el_Interval, is_continuous, is_extended_real, all_le):
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_continuous
    fx, limit = of_continuous(is_continuous)
    x, a, b = limit

    from Lemma.Calculus.Any.Le.Rolle.of.Lt.IsContinuous.IsExtendedReal.IsExtendedReal.Eq import is_differentiable_at
    S[fx], S[limit] = is_differentiable_at(is_extended_real)

    c, S[Interval.open(a, b)] = el_Interval.of(Element)
    (S[fx], S[fx._subs(x, c)]), S[limit] = all_le.of(All[LessEqual])
    return Subs[x:c](Derivative[x + S.Infinitesimal](fx)) <= 0


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Logic

    a, b, x, c = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        Element(c, Interval.open(a, b)),
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](f(x) <= f(c)))

    Eq <<= Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided), Algebra.AllIn_Ico.of.AllIn_Ico.offset.apply(Eq[-2], c)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Set.InSub.of.In_Icc.apply(Eq[0], c)

    Eq.gt_zero = Set.Lt.of.In_Icc.apply(Eq[-1]).this.apply(Algebra.Gt_0.of.Lt)

    Eq << Logic.ImpAnd.of.Imp.cond.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Set.In.In.given.And.In)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.of.Le)

    Eq << Logic.Imp.And.of.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.LeDiv.of.IsPositive.Le)

    Eq << Logic.All.of.Imp.apply(Eq[-1])

    Eq << Set.IsPositive.of.Gt_0.apply(Eq.gt_zero, simplify=None)

    δ = Symbol(real=True, positive=True)
    Eq << Set.Any.Eq.of.In.apply(Eq[-1], var=δ)

    Eq << Logic.Any_And.of.Any.All.apply(Eq[-3], Eq[-1], simplify=None)

    Eq.Any_All = Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[2])

    Eq << Eq[-1].subs(x, c)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided, simplify=2)

    Eq << Eq.Any_All.this.find(All).limits_subs(x, Eq[-1].lhs.variable)

    Eq << Logic.Any_And.of.Any.All.apply(Eq[-1], Eq.Any_All, simplify=None)

    Eq << Eq[-1].this.expr.apply(Calculus.Le_0.Limit.of.IsExtendedReal.All_Le.one_sided)




if __name__ == '__main__':
    run()
# created on 2023-10-15
