from util import *


@apply
def apply(given, scale):
    lhs, rhs = given.of(Greater)
    return lhs * scale < rhs * scale, scale < 0


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), z)
    Eq << Algebra.GtDiv.of.Lt_0.Lt.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-07-15
