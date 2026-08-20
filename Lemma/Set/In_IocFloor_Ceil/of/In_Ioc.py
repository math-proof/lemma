from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Ceil(b)

    a = Floor(a)
    return Element(x, Interval(a, b, **domain.kwargs))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << Subset(Interval(a, b, left_open=True), Interval(Floor(a), Ceil(b), left_open=True), plausible=True)

    Eq << Set.Subset.given.All_In.apply(Eq[-1])

    Eq << Set.In.of.In.Subset.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-29
