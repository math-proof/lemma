from util import *


@apply
def apply(given):
    n, interval = given.of(NotElement)
    a, S[n + 1] = interval.of(Range)
    return LessEqual(n, a - 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    n, a = Symbol(integer=True, given=True)
    Eq << apply(NotElement(n, Range(a, n + 1)))

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_Add_1.of.Gt.apply(Eq[-1])

    Eq << Set.In.Ico.of.Ge.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-06-06
