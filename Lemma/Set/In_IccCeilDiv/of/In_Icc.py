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
    from Lemma import Set, Algebra, Nat, Int

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(d * x, Range(a, b + 1)), d)

    Eq << Set.Ge.Le_Sub_1.of.In_Ico.apply(Eq[0])

    Eq << Nat.Le_Sub_1.of.Lt.apply(Eq[-1])

    Eq <<= Eq[-3] / d, Eq[-1] / d

    Eq <<= Int.LeCeil.of.Le.apply(Eq[-2]), Int.GeFloor.of.Ge.apply(Eq[-1])

    Eq << Set.In_Ico.of.Ge.Le.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-24
