from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert lhs.is_integer
    return Greater(lhs, rhs - 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x >= y)

    Eq << Nat.Ge_Add_1.of.Gt.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-05-23
