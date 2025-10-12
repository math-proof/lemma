from util import *


@apply
def apply(ne, le):
    x, a = ne.of(Unequal)
    S[x], b = le.of(LessEqual)
    assert a < b
    return x < a


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    a, x = Symbol(real=True)
    Eq << apply(Unequal(x, a), x <= a + 1)

    Eq << Algebra.Ne.of.Lt.apply(Eq[2])

    Eq << Nat.Le.of.Lt.apply(Eq[2])

    Eq << Algebra.Le.of.Le.relax.apply(Eq[-1], a + 1)


if __name__ == '__main__':
    run()
# created on 2023-04-13
