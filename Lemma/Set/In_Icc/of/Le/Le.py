from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(LessEqual)
    _x, b = _greater_than.of(GreaterEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    return Element(x, Interval(b, a))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True, given=True)
    # Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, x >= a)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2018-04-07

