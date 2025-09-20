from util import *


@apply
def apply(lt, le):
    x, a = lt.of(Less)
    b, _x = le.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
        left_open = True
        right_open = False
    else:
        left_open = False
        right_open = True

    return Element(x, Interval(b, a, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True)
    Eq << apply(a < x, x <= b)

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2021-05-30
