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

    Eq << Set.Icc_Ne_Empty.given.Gt.apply(Eq[0])

    Eq << Eq[-1] - a






if __name__ == '__main__':
    run()
# created on 2021-05-09
