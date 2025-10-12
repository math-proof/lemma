from util import *


@apply
def apply(el, n):
    x, domain = el.of(Element)
    S[-1], S[0] = domain.of(Interval)
    assert domain.left_open and domain.right_open
    return Equal(Limit[n:oo](x ** n), Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Calculus, Nat, Nat

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 0, left_open=True, right_open=True)), n)

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[0])

    Eq << Set.Lt.of.In_Icc.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Lt_0.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq.is_zero = Calculus.Eq_0.Limit.of.In_Icc.geometric_series.positive.apply(Eq[-1], n)

    Eq <<= Algebra.Ge_NegAbs.apply(Eq[1].find(Pow)), Algebra.Le_Abs.apply(Eq[1].find(Pow))

    Eq <<= Calculus.GeLimit.of.Ge.apply(Eq[-2], (n, oo)), Calculus.LeLimit.of.Le.apply(Eq[-1], (n, oo))

    Eq << Eq[-2].this.rhs.apply(Calculus.Limit.eq.Mul)

    Eq <<= Eq[-2].subs(Eq.is_zero), Eq[-1].subs(Eq.is_zero)

    Eq << Nat.Eq.of.Ge.Le.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2023-04-17
