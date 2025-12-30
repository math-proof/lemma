from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Interval)

    if S.left_open:
        lower_bound = e <= start
    else:
        lower_bound = e < start
    if S.right_open:
        upper_bound = e >= stop
    else:
        upper_bound = e > stop

    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from Lemma import Set

    e, a, b = Symbol(real=True, given=True)
    Eq << apply(NotElement(e, Interval(a, b)))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(Set.In_Icc.of.Le.Le)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-10-09
