from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(0, 1, left_open=True, right_open=True)
    assert domain_y in Interval(0, 1, left_open=True, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(0, 1, left_open=True, right_open=True)), Element(y, Interval(0, 1, left_open=True, right_open=True)))

    Eq << Greater(y ** 2 * (1 - x ** 2), x ** 2 * (1 - y ** 2), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq.x_is_positive = Set.Gt_0.of.IsPositive.apply(Eq[1])

    Eq.y_is_positive = Set.Gt_0.of.IsPositive.apply(Eq[2])

    Eq << Eq.y_is_positive + Eq.x_is_positive

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Algebra.Gt.of.Gt_0.apply(Eq[-1])

    Eq << Set.Sqrt.gt.Zero.of.In.apply(Eq[2])

    Eq << Algebra.Gt_0.Square.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.Square.of.Gt_0.apply(Eq.x_is_positive)

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Ge_0.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GtSqrt.of.Ge_0.Gt.apply(Eq[-1], Eq[4])

    Eq <<= Algebra.EqAbs.of.Gt_0.apply(Eq.x_is_positive), Algebra.EqAbs.of.Gt_0.apply(Eq.y_is_positive)
    Eq << Eq[-3].subs(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-11-27
