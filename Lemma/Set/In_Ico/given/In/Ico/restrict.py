from util import *


@apply
def apply(imply, upper=None, lower=None):
    x, interval = imply.of(Element)
    a, b = interval.of(Range)
    if upper is not None:
        assert upper <= b or upper - b <= 0
        b = upper
    elif lower is not None:
        assert lower >= a or lower - a >= 0
        a = lower

    return Element(x, Range(a, b))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), upper=b - 1)

    Eq << Set.In.Ico.of.In_Ico.relax.apply(Eq[1], upper=b)




if __name__ == '__main__':
    run()
# created on 2023-08-20
