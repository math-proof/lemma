from util import *



@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    b, _x = _greater_than.of(LessEqual)
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

    a, b, x = Symbol(real=True, given=True)
    # Eq << apply(x > b, x <= a)
    Eq << apply(b > x, a <= x)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Eq[-1].reversed

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2018-05-14
