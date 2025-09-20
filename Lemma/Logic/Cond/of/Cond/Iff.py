from util import *


@apply
def apply(cond, equivalent):
    lhs, rhs = equivalent.of(Iff)
    if cond != lhs:
        lhs, rhs = rhs, lhs
    assert cond == lhs
    return rhs


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(LessEqual(f[0], g[0]), Iff(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])))

    Eq << Logic.Imp.of.Iff.apply(Eq[1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-17

