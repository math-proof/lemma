from util import *



@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)

    assert lhs.is_real
    assert rhs.is_real
    assert lhs >= 0

    return LessEqual(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x = Symbol(real=True, nonnegative=True)
    y = Symbol(real=True)

    Eq << apply(LessEqual(x, y))

    Eq << Nat.LeMulS.of.Le.Le.Ge_0.Ge_0.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

# created on 2018-07-03

del Ge
from . import Ge
