from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return Greater(b - a, 0)


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b, left_open=True), a.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1] + a

    Eq << Set.EqIcc.of.Le.apply(Eq[-1], left_open=True)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-09-16
