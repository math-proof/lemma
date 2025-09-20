from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return GreaterEqual(a, b)


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))

    Eq << ~Eq[1]

    Eq << Set.Icc_Ne_Empty.of.Lt.apply(Eq[-1], right_open=False)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-05-03
