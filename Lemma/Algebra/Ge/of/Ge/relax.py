from util import *


@apply
def apply(given, lower=None, upper=None):
    lhs, rhs = given.of(GreaterEqual)
    if lower is not None:
        assert rhs - lower >= 0 or rhs >= lower
        rhs = lower
    elif upper is not None:
        assert lhs - upper <= 0 or lhs <= upper
        lhs = upper

    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    z = Symbol(domain=Interval(-oo, y))
    Eq << apply(x >= y, z)

    Eq << GreaterEqual(y, z, plausible=True)

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-01
