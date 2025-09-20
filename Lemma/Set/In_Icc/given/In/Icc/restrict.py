from util import *


@apply
def apply(imply, upper=None, lower=None):
    x, interval = imply.of(Element)
    a, b = interval.of(Interval)
    if upper is not None:
        assert upper <= b or upper - b <= 0
        b = upper
    elif lower is not None:
        assert lower >= a or lower - a >= 0
        a = lower

    return Element(x, Interval(a, b, **interval.kwargs))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b)), lower=a + 1)

    Eq << Set.In.Icc.of.In_Icc.relax.apply(Eq[1], lower=a)




if __name__ == '__main__':
    run()
# created on 2023-08-20
