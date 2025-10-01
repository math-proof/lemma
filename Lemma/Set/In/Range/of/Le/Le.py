from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(LessEqual)
    b, _x = _greater_than.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    assert x.is_integer
    return Element(x, Range(b, a + 1))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, a <= x)

    Eq << Set.In_Ico.given.And.apply(Eq[-1])

    Eq << Eq[-2].reversed

    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-05-23
