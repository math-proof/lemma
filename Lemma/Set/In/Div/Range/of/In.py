from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])
    e /= d
    # assert e.is_integer

    b -= 1

    return Element(e, Range(start=ceil(a / d), stop=b // d + 1))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(d * x, Range(a, b + 1)), d)

    Eq << Set.And.of.In_Range.apply(Eq[0])

    Eq << Algebra.Le.of.Lt.strengthen.apply(Eq[-1])

    Eq <<= Eq[-3] / d, Eq[-1] / d

    Eq <<= Algebra.GeCeil.of.Ge.integer.apply(Eq[-2]), Algebra.LeFloor.of.Le.integer.apply(Eq[-1])

    Eq << Set.In.Range.of.Ge.Le.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-24
