from util import *


@apply
def apply(notcontains):
    x, ab = notcontains.of(NotElement)

    a, b = ab.of(Interval)

    assert ab.right_open

    return Equal(x, b) | NotElement(x, ab.copy(right_open=False))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Interval(a, b, right_open=True)))

    Eq << Set.NotIn_Ico.of.Or_NotIn_Icc.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-10-20
