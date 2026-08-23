from util import *


@apply
def apply(ou, reverse=False):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    y = abs(y)
    lhs, rhs = acos(x / r), Piecewise((asin(y / r), x >= 0), (S.Pi - asin(y / r), True))
    if reverse:
        lhs, rhs = rhs, lhs
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Bool, Real, Rat, Nat

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Eq[-1].this.lhs.apply(Real.Arccos.eq.Sub_Arcsin)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=x >= 0)

    Eq <<= Bool.Imp_Ite.given.Imp.apply(Eq[-2]), Bool.Imp_Ite.given.Imp.apply(Eq[-1], invert=True)

    Eq.x_is_nonnegative, Eq.x_is_negative = Eq[-2].this.find(acos).apply(Real.Arccos.eq.Ite_Arcsin_Sub_Arcsin), Eq[-1].this.find(acos).apply(Real.Arccos.eq.Ite_Arcsin_Sub_Arcsin)

    Eq.sqrt_is_positive = Real.GtSqrt_0.of.OrNeS_0.apply(Eq[0])

    Eq << Bool.Imp_And.of.Cond.apply(Eq.sqrt_is_positive, cond=Eq.x_is_nonnegative.lhs)

    Eq << Eq[-1].this.rhs.apply(Rat.GeDivS.of.Ge.Gt_0)

    Eq <<= Eq.x_is_nonnegative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Bool.And_BFnIte.given.And_BFn)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    Eq << Bool.Imp_And.of.Cond.apply(Eq.sqrt_is_positive, cond=Eq.x_is_negative.lhs)

    Eq << Eq[-1].this.rhs.apply(Nat.LtDiv.of.Gt_0.Lt)

    Eq <<= Eq.x_is_negative & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Bool.And_BFnIte.given.And_BFn, invert=True)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Add]).apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2020-12-03
