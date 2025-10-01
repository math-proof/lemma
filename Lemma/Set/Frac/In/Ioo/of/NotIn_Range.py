from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Element(frac(x), Interval(0, 1, left_open=True, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << Set.NeFrac_0.of.NotIn.apply(Eq[0])

    Eq << Element(frac(x), Interval(0, 1, right_open=True), plausible=True)

    Eq << Set.In_SDiff.of.In.Ne.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-05-17
