from util import *


@apply
def apply(le0, le1):
    x, a = le0.of(LessEqual)
    b, _x = le1.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x

    return Element(x, Interval(b, a, left_open=False, right_open=False))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True)
    Eq << apply(a <= x, x <= b)

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2021-05-22
