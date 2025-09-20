from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, S[-a] = domain.of(Interval)
    assert domain.is_open

    return x ** 2 < a ** 2


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a = Symbol(real=True)
    Eq << apply(Element(x, Interval(-a, a, left_open=True, right_open=True)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Gt.of.Gt.Lt.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[-1]) / 2

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.LtSquare.given.And.Lt.apply(Eq[1])

    Eq <<= Eq[-2].subs(Eq[-3]), Eq[-1].subs(Eq[-3])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-11-26
