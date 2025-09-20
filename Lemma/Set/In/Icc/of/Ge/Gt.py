from util import *


@apply
def apply(greater_than, strict_greater_than):
    a, x = greater_than.of(GreaterEqual)
    _x, b = strict_greater_than.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
        left_open = False
        right_open = True
    else:
        left_open = True
        right_open = False

    return Element(x, Interval(b, a, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True, given=True)
    # Eq << apply(x >= b, a > x)
    Eq << apply(b >= x, x > a)

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[-1])



    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-08
