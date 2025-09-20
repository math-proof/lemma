from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    assert lhs.is_integer and rhs.is_integer
    return GreaterEqual(lhs - 1, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[0]) - 1


if __name__ == '__main__':
    run()
# created on 2019-07-23
