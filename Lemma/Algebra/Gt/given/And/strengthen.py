from util import *


@apply
def apply(given, upper, strict=False):
    lhs, rhs = given.of(Greater)
    if strict:
        return lhs >= upper, upper > rhs
    return lhs > upper, upper >= rhs


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), z, strict=True)

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2019-07-01
