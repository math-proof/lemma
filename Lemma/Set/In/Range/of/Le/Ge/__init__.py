from util import *


@apply
def apply(le, ge):
    x, a = le.of(LessEqual)
    _x, b = ge.of(GreaterEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
    assert x.is_integer
    return Element(x, Range(b, a + 1))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, x >= a)

    Eq << Set.In_Range.given.And.apply(Eq[-1])



    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-25
from . import In
