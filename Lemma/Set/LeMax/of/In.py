from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return abs(x) <= b


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Le_Abs.given.And.apply(Eq[1])

    Eq << Algebra.Le_Abs.apply(b)

    Eq << LessEqual(abs(b), Max(abs(a), abs(b)), plausible=True)

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Le.of.Le.Le.apply(Eq[3], Eq[-1])

    Eq << Algebra.Ge_NegAbs.apply(a)

    Eq << GreaterEqual(-abs(a), -Max(abs(a), abs(b)), plausible=True)

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[-2], Eq[-1])
    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-30
