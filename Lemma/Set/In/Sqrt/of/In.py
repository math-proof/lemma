from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a >= 0
    return Element(sqrt(x), domain.copy(start=sqrt(a), stop=sqrt(b)))


@prove
def prove(Eq):
    from Lemma import Set, Real

    x = Symbol(real=True)
    a, b = Symbol(real=True, nonnegative=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[1])

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq << Real.GeSqrt.of.Ge.apply(Eq[-2])

    Eq << Set.Ge.of.Ge.In_Iic.apply(Eq[-2], lower=0)

    Eq << Real.LtSqrt.of.Ge_0.Lt.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2019-06-28


