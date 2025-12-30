from util import *


@apply
def apply(given, upper=None, lower=None):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    if upper is not None:
        assert upper >= b or upper - b >= 0
        b = upper
    elif lower is not None:
        assert lower <= a or lower - a <= 0
        a = lower

    return Element(x, Interval(a, b, **interval.kwargs))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b)), lower=a - 1)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[1])

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Ge.of.Ge.relax.apply(Eq[-1], lower=a - 1)




if __name__ == '__main__':
    run()
# created on 2023-08-20
