from util import *


@apply
def apply(el, is_finite):
    γ, domain = el.of(Element)
    fk, (k, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert k.is_integer
    S[0], S[1] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    return Element(Sum[k:oo](γ ** k * fk), Interval(-oo, oo))



@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Nat, Int

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[k:oo](Abs(r[k])), oo))

    Eq << Algebra.All_Le_Sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Gt_0.Pow.of.Gt_0.apply(Eq.gt_zero, k)

    Eq << Algebra.Gt_0.Abs.of.Gt_0.apply(Eq[-1])

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[-3])

    n = Symbol(integer=True, positive=True)
    Eq << Algebra.LeSum.of.Le.apply(Eq[-1], (k, 0, n))

    Eq << Algebra.AbsSum.le.Sum_Abs.apply(Eq[2].find(Sum)._subs(oo, n))

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-1], Eq[-2])

    Eq << Int.EqAbs.of.Gt_0.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Ne.of.Lt.apply(Eq.lt)

    Eq << Algebra.EqSum.of.Ne.geometric_series.apply(Eq[-1], Eq[-2].rhs.find(Sum))

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Algebra.And.of.LeAbs.apply(Eq[-1])

    Eq <<= Calculus.LeLimit.of.Le.apply(Eq[-2], (n, oo)), Calculus.GeLimit.of.Ge.apply(Eq[-1], (n, oo))

    Eq <<= Eq[-2].this.lhs.apply(Calculus.Limit.eq.Sum), Eq[-1].this.lhs.apply(Calculus.Limit.eq.Sum)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Limit.eq.Mul), Eq[-1].this.rhs.apply(Calculus.Limit.eq.Mul)

    Eq.upper_bound, Eq.lower_bound = Eq[-2].this.find(Limit).apply(Calculus.Limit.eq.Mul), Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Mul)

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq.gt_zero, -1)

    Eq << Algebra.LtAbs.of.Gt.Lt.apply(Eq[-1], Eq.lt)

    Eq << Calculus.Eq_0.Limit.of.LtAbs.geometric_series.apply(Eq[-1], n)

    Eq.upper_bound = Eq.upper_bound.subs(Eq[-1])

    Eq.lower_bound = Eq.lower_bound.subs(Eq[-1])

    Eq << -Eq.lt + 1

    Eq << Algebra.LtDiv.of.Gt_0.Lt.apply(Eq[-1], Eq[1], simplify=False)

    Eq << -Eq[-1]

    Eq <<= Nat.Lt.of.Le.Lt.apply(Eq.upper_bound, Eq[-2]), Nat.Gt.of.Ge.Gt.apply(Eq.lower_bound, Eq[-1])

    Eq << Algebra.LtAbs.of.Lt.Gt.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    Eq << Set.IsReal.of.Abs_Lt_Infty.apply(Eq[-1], simplify=None)





if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-04-16
from . import negative
