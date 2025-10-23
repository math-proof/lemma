from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    assert rhs > 0

    return Greater(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Bool, Nat

    x = Symbol(real=True, given=True)
    y = Symbol(positive=True, given=True)
    Eq << apply(Greater(x, y))

    Eq << GreaterEqual(y, 0, plausible=True)

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[0], Eq[-1])

    Eq << Nat.Ne.of.Gt.apply(Eq[-1])

    Eq <<= ~Eq[1] & Eq[-1]

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Algebra.LeExp.of.Le.apply(Eq[-1])

    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01
