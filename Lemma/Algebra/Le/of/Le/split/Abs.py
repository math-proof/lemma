from util import *


@apply
def apply(given, negate=False):
    x, M = given.of(LessEqual)
    x = x.of(Abs)
    if negate:
        x = -x
    return LessEqual(x, M)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Int, Int
    M, a = Symbol(real=True)

    Eq << apply(LessEqual(abs(a), M), negate=True)

    Eq << Int.GeAbs.apply(a, negate=True)

    Eq << Nat.Le.of.Le.Le.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-04-15
