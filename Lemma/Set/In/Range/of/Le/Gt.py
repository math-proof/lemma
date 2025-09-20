from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(greater_than, strict_greater_than):
    x, a = greater_than.of(LessEqual)
    _x, b = strict_greater_than.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
    else:
        a += 1
        b += 1

    assert x.is_integer
    return Element(x, Range(b, a))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(x >= b, a > x)
    Eq << apply(x <= b, x > a)

    Eq << Set.In_Range.given.And.apply(Eq[-1])

    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[-2])

    # Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-05-21
