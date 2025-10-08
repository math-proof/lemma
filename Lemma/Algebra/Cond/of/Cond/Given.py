from util import *


@apply
def apply(cond, necessary):
    lhs, rhs = necessary.of(Given)
    assert cond == rhs

    return lhs


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True, given=True)
    f, g = Symbol(integer=True, shape=(oo,), given=True)
    Eq << apply(LessEqual(f[0], g[0]), Given(LessEqual(f[n], g[n]), LessEqual(f[0], g[0])))

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[1].reversed)








if __name__ == '__main__':
    run()
# created on 2018-11-11

