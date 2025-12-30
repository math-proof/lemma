from util import *


@apply
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(x) + asin(sqrt(1 - x ** 2)), S.Pi / 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra, Set, Bool, Int

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x >= 0)

    Eq << Trigonometry.Cos.eq.Sub.apply(cos(Eq[1].lhs))

    Eq << Int.EqAbs.of.Ge_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.any_eq = Trigonometry.Any.Eq.of.Cos.eq.Zero.apply(Eq[-1])

    Eq << LessEqual(x, 1, plausible=True)

    Eq << Set.In_Icc.of.Le.Le.apply(Eq[-1], Eq[0])

    Eq <<= Trigonometry.In.Arcsin.of.In.apply(Eq[-1]), Set.In.Sqrt.Max.of.In.apply(Eq[-1])

    Eq << Trigonometry.In.Arcsin.of.In.apply(Eq[-1])

    Eq << Set.Add.In.Ioc.of.In.In.apply(Eq[-1], Eq[-3])

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.find(Element).apply(Set.InSub.of.In_Icc, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(Set.InDiv.of.In_Icc, S.Pi)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-09
