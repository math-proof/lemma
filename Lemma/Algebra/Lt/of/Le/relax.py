from util import *


@apply
def apply(given, upper=None, lower=None, step=1):
    lhs, rhs = given.of(LessEqual)
    if upper is not None:
        assert rhs < upper
        rhs = upper
    elif lower is not None:
        assert lower < lhs
        lhs = lower
    elif step > 0:
        rhs += step
    elif step < 0:
        lhs += step

    return Less(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(real=True)
    Eq << apply(x <= a, step=1)

    Eq << Less(a, a + 1, plausible=True)

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-02-27
# updated on 2023-11-05
