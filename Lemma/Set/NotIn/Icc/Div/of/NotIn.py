from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(NotElement)

    a, b = interval.of(Interval)

    return NotElement(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    from Lemma import Set
    x, a, b = Symbol(real=True, given=True)
#     t = Symbol(real=True)
    d = Symbol(real=True, given=True, positive=True)

    Eq << apply(NotElement(x, Interval(a, b)), d)

    Eq << ~Eq[-1]

    Eq << Set.In.Mul.Icc.of.In.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

# created on 2021-06-07
