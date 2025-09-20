from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Expr ** 2)
    assert x.is_real
    return LessEqual(x, sqrt(a)), LessEqual(-sqrt(a), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(real=True)
    Eq << apply(x ** 2 <= a ** 2)

    Eq << Algebra.LeAbs.of.Le.Ge.apply(Eq[-2], Eq[-1].reversed)

    Eq << Algebra.LeSquare.of.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-18
