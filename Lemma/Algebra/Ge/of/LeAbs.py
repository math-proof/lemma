from util import *


@apply
def apply(given, negate=False):
    x, M = given.of(LessEqual)
    x = x.of(Abs)
    if negate:
        x = -x
    assert x.is_extended_real
    return GreaterEqual(x, -M)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    M, a = Symbol(real=True)
    Eq << apply(LessEqual(abs(a), M), negate=True)

    Eq << Algebra.Le_Abs.apply(a)

    Eq << Nat.Le.of.Le.Le.apply(Eq[-1], Eq[0])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-04-16
