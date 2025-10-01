from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << Set.Lt.of.Lt.In.apply(Eq[0], Eq[2])

    Eq.x_contains = Set.In.Icc.Inter.of.Lt.In_Icc.apply(Eq[-1], Eq[1])

    Eq << Set.Gt.of.Gt.In.apply(Eq[0].reversed, Eq[1])

    Eq.y_contains = Set.In.Icc.Inter.of.Gt.In_Icc.apply(Eq[-1], Eq[2])

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[3], cond=Equal(x, -1))

    Eq << Logic.Imp.given.ImpEq.apply(Eq[-2])

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << -Set.LtSquare.of.In.apply(Eq.y_contains) + 1

    Eq << Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-1])

    Eq << Logic.Imp.of.Cond.apply(Eq.x_contains, cond=Eq[-4].lhs)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.In_SDiff.of.In.Ne)

    Eq << Logic.Imp_And.of.Cond.Imp.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Set.Gt.Sqrt.Ioo.of.Lt.In.In)


if __name__ == '__main__':
    run()
# created on 2020-11-29
