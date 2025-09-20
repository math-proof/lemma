from util import *


@apply
def apply(gt, lt):
    a, x = gt.of(Greater)
    b, _x = lt.of(Less)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    assert b.is_integer
    b += 1
    assert x.is_integer
    return Element(x, Range(b, a))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    Eq << apply(x > b, x < a)

    # Eq << apply(b > x, a < x)
    Eq << Set.In_Range.given.And.apply(Eq[-1])



    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[-1])

    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-20
