from util import *


@apply
def apply(lt, gt):
    a, x = lt.of(Less)
    b, _x = gt.of(Greater)
    if x != _x:
        b, x, a, S[x] = x, a, _x, b
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a < x, b > x)

    Eq << Eq[1].reversed

    Eq << Algebra.Lt.of.Lt.Lt.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-11

