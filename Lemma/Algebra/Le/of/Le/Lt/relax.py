from util import *


@apply
def apply(le, lt):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, S[x], b = _x, b, a, x

    return LessEqual(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True, given=True)
    Eq << apply(a <= x, x < b)

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[0], Eq[1])

    Eq << Algebra.Le.of.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-11-24
