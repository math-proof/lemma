from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(greater_than, strict_greater_than):
    x, a = greater_than.of(LessEqual)
    b, _x = strict_greater_than.of(Less)
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
    Eq << apply(x <= b, a < x)

    Eq << Set.In_Range.given.And.apply(Eq[-1])

    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[-2])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-05-25
