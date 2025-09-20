from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])

    e *= d

    return Element(e, Range(a * d, (b - 1) * d + 1))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b)), d)

    Eq << Set.And.of.In_Range.apply(Eq[0], right_open=False)

    Eq <<= Eq[-1] * d, Eq[-2] * d

    Eq << Set.In.Range.of.Ge.Le.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2018-05-26


from . import dilated
