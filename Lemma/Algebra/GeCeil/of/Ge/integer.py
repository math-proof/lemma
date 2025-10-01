from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    assert x.is_integer
    assert y.is_real

    return GreaterEqual(x, ceil(y))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(integer=True, given=True)
    y = Symbol(real=True, given=True)

    Eq << apply(x >= y)

    Eq << ~Eq[1]

    Eq << Algebra.Le_Sub_1.of.Lt.apply(Eq[-1])

    Eq << Algebra.Le.of.Ge.Le.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed - (y - 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Frac)


if __name__ == '__main__':
    run()

# created on 2018-05-22
