from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Element(x, Interval(-a, a))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Algebra.And.of.LeAbs.apply(Eq[0])
    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-01-07
