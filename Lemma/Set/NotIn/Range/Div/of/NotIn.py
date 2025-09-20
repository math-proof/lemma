from util import *


@apply
def apply(given, d):

    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, interval = given.of(NotElement)

    a, b = interval.of(Range)
    e /= d

    assert e.is_integer
    b -= 1

    return NotElement(e, Range(start=ceil(a / d), stop=b // d + 1))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a, b = Symbol(integer=True, given=True)
    d = Symbol(integer=True, positive=True, given=True)
    Eq << apply(NotElement(d * x, Range(a, b + 1)), d)

    Eq << ~Eq[-1]

    Eq.contains = Set.In.Mul.Range.of.In.apply(Eq[-1], d)

    Eq << Algebra.LeFloor.apply(b / d) * d

    Eq << Algebra.GeCeil.apply(a / d) * d

    Eq << Set.Subset.Range.of.Le.Ge.apply(Eq[-2], Eq[-1])

    Eq << Set.In.of.In.Subset.apply(Eq.contains, Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-06-08
