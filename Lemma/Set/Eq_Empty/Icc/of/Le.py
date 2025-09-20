from util import *


@apply
def apply(given, left_open=False, right_open=False):
    b, a = given.of(LessEqual)

    if left_open or right_open:
        ...
    else:
        right_open = True

    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y, right_open=True)

    Eq << Eq[0].reversed

    Eq << Set.Eq_Empty.Icc.of.Ge.apply(Eq[-1], right_open=True)


if __name__ == '__main__':
    run()
# created on 2019-07-09
