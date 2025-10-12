from util import *


@apply
def apply(given, m):
    lhs, rhs = given.of(Greater)
    return GreaterEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    x, y, z = Symbol(real=True, given=True)

    Eq << apply(x > y, z)
    Eq << Nat.Ge.of.Gt.apply(Eq[0])

    Eq << Algebra.GeMin.of.Ge.apply(Eq[-1], z)

if __name__ == '__main__':
    run()
# created on 2019-07-22
