from util import *


@apply
def apply(given):
    x, y = given.of(Greater)
    assert y.is_integer
    return GreaterEqual(floor(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, given=True)
    y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << Algebra.Floor.gt.Sub_1.apply(x)

    Eq << Eq[0] - 1

    Eq << Algebra.Gt.of.Gt.Gt.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Ge_Add_1.of.Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-20
