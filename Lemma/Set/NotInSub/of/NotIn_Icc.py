from util import *


@apply
def apply(given, t):
    e, interval = given.of(NotElement)

    a, b = interval.args

    return NotElement(e - t, interval.copy(start=a - t, stop=b - t))


@prove
def prove(Eq):
    from Lemma import Set
    x, a, b, t = Symbol(real=True, given=True)

    Eq << apply(NotElement(x, Interval(a, b)), t)

    Eq << ~Eq[-1]

    Eq << Set.InAdd.of.In_Icc.apply(Eq[-1], t)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-07-11
