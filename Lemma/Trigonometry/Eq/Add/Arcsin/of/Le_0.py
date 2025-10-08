from util import *


@apply
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Set, Bool

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x <= 0)

    Eq << Trigonometry.Cos.eq.Sub.apply(cos(Eq[1].lhs))

    Eq << Algebra.EqAbs.of.Le_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Cos.Neg)
    Eq << Trigonometry.Any.Eq.of.Cos.eq.Zero.apply(Eq[-1])

    Eq << -Eq[-1].this.expr

    Eq << Eq[-1].this.apply(Algebra.Any.limits.Neg.Infty)

    Eq << Algebra.AnyIn_Ico.of.AnyIn_Ico.offset.apply(Eq[-1], 1)

    Eq.any_eq = Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << GreaterEqual(x, -1, plausible=True)

    Eq << Set.In.Icc.of.Ge.Le.apply(Eq[-1], Eq[0])

    Eq <<= Trigonometry.In.Arcsin.of.In.apply(Eq[-1]), Set.In.Sqrt.Max.of.In.apply(Eq[-1])

    Eq <<= Set.Neg.In.Icc.of.In_Icc.apply(Eq[-2]), Trigonometry.In.Arcsin.of.In.apply(Eq[-1])

    Eq << Set.Add.In.Ioc.of.In.In.apply(Eq[-1], Eq[-2])

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.find(Element).apply(Set.InSub.of.In_Icc, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(Set.InDiv.of.In_Icc, S.Pi)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)



if __name__ == '__main__':
    run()
# created on 2018-07-13
# updated on 2023-05-20
