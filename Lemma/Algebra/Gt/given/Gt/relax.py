from util import *


@apply
def apply(given, lower=None, upper=None):
    lhs, rhs = given.of(Greater)
    if lower is not None:
        assert lower <= lhs
        lhs = lower
    elif upper is not None:
        assert upper >= rhs
        rhs = upper

    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), x - 1)

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[1], upper=x)


if __name__ == '__main__':
    run()
# created on 2019-07-16
