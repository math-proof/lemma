from util import *



@apply
def apply(given, d):
    e, interval = given.of(NotElement)
    d = sympify(d)
    assert d.is_positive

    a, b = interval.of(Interval)

    e *= d

    return NotElement(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    from Lemma import Set
    x, a, b = Symbol(real=True, given=True)

    d = Symbol(real=True, positive=True, given=True)

    Eq << apply(NotElement(x, Interval(a, b, right_open=True)), d)

    Eq << ~Eq[-1]

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

# created on 2021-06-07
