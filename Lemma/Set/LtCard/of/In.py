from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, S[-a] = domain.of(Interval)
    assert domain.is_open
    return abs(x) < -a


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, a = Symbol(real=True)
    Eq << apply(Element(x, Interval(-a, a, left_open=True, right_open=True)))

    Eq << Algebra.Lt_Abs.given.And.apply(Eq[1])
    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-03-12
