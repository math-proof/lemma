from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)
    assert lhs >= 0
    return Less(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Less(x * x, y * y))

    Eq << ~Eq[1]

    Eq << Algebra.GeSquare.of.Ge.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2019-06-30
