from util import *


@apply
def apply(given, t):
    e, interval = given.of(Element)
    assert t.is_finite
    return Element(e + t, interval + t)


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq <<= Eq[-1] + t, Eq[-2] + t

    Eq << Set.In_Icc.of.Le.Ge.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-08
