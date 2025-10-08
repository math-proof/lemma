from util import *


@apply
def apply(given, pivot):
    x, a = given.of(LessEqual)
    assert pivot.is_real
    return Or(LessEqual(x, a) & GreaterEqual(x, pivot), Less(x, pivot))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z)

    Eq << ~Eq[-1]

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1], invert=True)


if __name__ == '__main__':
    run()
# created on 2019-11-18
