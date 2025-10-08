from util import *


@apply
def apply(inter0, inter1):
    p0, q0 = inter0.of(Imply)
    p1, q1 = inter1.of(Imply)
    assert p0 | p1
    return p0 & q0 | p1 & q1


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p0, q0, p1, q1 = Symbol(bool=True)
    a, b = Symbol(integer=True)
    Eq << apply((a > b) >> q0, (a <= b) >> q1)

    Eq << Or(a > b, a <= b, plausible=True)

    Eq << Bool.Or.of.Or.Imp.Imp.apply(Eq[-1], Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
