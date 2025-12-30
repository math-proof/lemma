from util import *


@apply
def apply(given, left_open=True, right_open=True):
    x, y = given.of(Less)

    return Element((x + y) / 2, Interval(x, y, right_open=right_open, left_open=left_open))


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(a < b)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq <<= Eq[-2] * 2, Eq[-1] * 2

    Eq <<= Eq[-2] - a, Eq[-1] - b
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-06-21
