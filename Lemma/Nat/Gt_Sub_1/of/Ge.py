from util import *


@apply
def apply(given, lower=None, upper=None, step=-1):
    lhs, rhs = given.of(GreaterEqual)
    if upper is not None:
        assert upper - lhs > 0
        lhs = upper
    elif lower is not None:
        assert rhs - lower > 0
        rhs = lower
    elif step > 0:
        lhs += step
    elif step < 0:
        rhs += step

    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y, y - 1)

    Eq << Greater(y, y - 1, plausible=True)

    Eq << Nat.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-05-29
# updated on 2023-11-05
