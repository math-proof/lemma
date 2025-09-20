from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Element(x, Interval(-a, a))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.LeAbs.of.Le.Ge.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-01-06
