from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Less)

    assert lhs.is_real
    assert rhs.is_real
    assert lhs >= 0

    return Less(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, nonnegative=True)
    y = Symbol(real=True)

    Eq << apply(Less(x, y))

    Eq << Algebra.LtMul.of.Lt.Lt.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

# created on 2020-01-01

del Gt
from . import Gt
