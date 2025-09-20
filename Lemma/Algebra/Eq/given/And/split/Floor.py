from util import *


@apply
def apply(given):
    y, floor_x = given.of(Equal)
    if not floor_x.is_Floor:
        y, floor_x = floor_x, y
    assert y.is_integer
    x = floor_x.of(Floor)
    return x - 1 < y, y <= x


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    y = Symbol(integer=True)
    Eq << apply(Equal(y, floor(x)))

    Eq << Algebra.Eq.of.Lt.Le.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2019-03-29
