from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    _x, b = gt.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,


    return Element(x, Interval(b, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True, given=True)
    # Eq << apply(b < x, a >= x)
    Eq << apply(x < b, x > a)

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[-1])

    # Eq << Eq[-1].reversed
    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2020-05-07
