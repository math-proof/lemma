from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return Element(sqrt(b ** 2 - x ** 2), Interval(0, b))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])

    Eq << Set.LeMax.of.In.apply(Eq[0])

    Eq << Algebra.LeSquare.of.Le.apply(Eq[-1]).reversed

    Eq << Algebra.Ge_0.of.Ge.apply(Eq[-1])

    Eq << Algebra.GeSqrt_0.of.Ge_0.apply(Eq[-1])

    Eq << LessEqual(-x ** 2, 0, plausible=True)

    Eq << Algebra.LeAdd.of.Le.apply(Eq[-1], Max(abs(a), abs(b)) ** 2)

    Eq << Algebra.LeSqrt.of.Ge_0.Le.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-08
