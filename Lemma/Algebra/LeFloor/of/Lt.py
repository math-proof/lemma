from util import *


@apply
def apply(lt):
    x, y = lt.of(Less)
    assert x.is_integer
    return LessEqual(x, Floor(y))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x = Symbol(integer=True)
    y = Symbol(real=True)
    Eq << apply(x < y)

    Eq << Nat.Le.of.Lt.apply(Eq[0])
    Eq << Algebra.LeFloor.of.Le.integer.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-02
