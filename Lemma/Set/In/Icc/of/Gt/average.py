from util import *


@apply
def apply(given, left_open=True, right_open=True):
    y, x = given.of(Greater)

    return Element((x + y) / 2, Interval(x, y, right_open=right_open, left_open=left_open))


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(a > b)

    Eq << Set.In.Icc.of.Lt.average.apply(Eq[0].reversed)




if __name__ == '__main__':
    run()
# created on 2021-04-16
