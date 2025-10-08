from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return acos(x) > acos(y)


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Set, Bool

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << Algebra.Gt.given.Gt_0.apply(Eq[3])

    Eq << Trigonometry.Sin.eq.Sub.apply(sin(Eq[-1].lhs))

    Eq << Set.GtSqrt.of.Lt.In.In.apply(Eq[0], Eq[1], Eq[2])

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[-1])

    Eq.sin_is_positive = Algebra.Gt.of.Eq.Gt.subst.apply(Eq[-3], Eq[-1])

    Eq << Trigonometry.Arccos.In.Icc.apply(x)

    Eq << Trigonometry.Arccos.In.Icc.apply(y)

    Eq << Set.Sub.In.Ioc.of.In.In.apply(Eq[-2], Eq[-1])

    Eq << Set.Or.of.In_Icc.apply(Eq[-1], 0, left_open=True)

    Eq << Eq[-1].this.args[1].apply(Trigonometry.Le_0.Sin.of.In_Icc)

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq.sin_is_positive, Eq[-1])

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-30
