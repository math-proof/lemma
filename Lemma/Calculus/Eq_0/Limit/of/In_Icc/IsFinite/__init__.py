from util import *


@apply
def apply(el, is_finite):
    λ, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    fn, (n, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert n.is_integer
    return Equal(Limit[n:oo](λ ** n * fn), Zeros(*fn.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Nat

    x = Symbol(real=True, shape=(oo,))
    γ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[n:oo](Abs(x[n])), oo))

    Eq << Algebra.All_Le_Sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Gt_0.Pow.of.Gt_0.apply(Eq.gt_zero, n)

    Eq << Algebra.Gt_0.Abs.of.Gt_0.apply(Eq[-1])

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[-3])

    Eq <<  Calculus.LeLimit.of.Le.apply(Eq[-1], (n, oo))

    Eq.le = Eq[-1].this.rhs.apply(Calculus.Limit.eq.Mul)

    Eq << Calculus.Eq_0.Limit.of.In_Icc.geometric_series.positive.apply(Eq[0], n)

    Eq << Set.IsReal.of.Eq_0.apply(Eq[-1])

    Eq << Calculus.Eq.Abs.Limit.of.IsLimited.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq.le.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(Algebra.MulAbsS.eq.AbsMul)

    Eq << GreaterEqual(Eq[-1].lhs.expr, 0, plausible=True)

    Eq << Calculus.GeLimit.of.Ge.apply(Eq[-1], (n, oo))

    Eq << Nat.Eq.of.Ge.Le.apply(Eq[-1], Eq[-3])

    Eq << Calculus.Limit.eq.Zero.of.LimitAbs.eq.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18



from . import negative
