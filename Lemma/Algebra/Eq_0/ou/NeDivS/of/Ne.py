from util import *



@apply
def apply(given, d):
    lhs, rhs = given.of(Unequal)
    return Unequal(lhs / d, rhs / d) | Equal(d, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x, y, d = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, y), d)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(Nat.EqMulS.of.Eq)

    Eq <<= ~Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-02-06
