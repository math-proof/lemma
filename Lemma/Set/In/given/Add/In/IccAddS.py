from util import *


@apply
def apply(imply, c):
    e, interval = imply.of(Element)
    assert c.is_finite

    return Element(e + c, interval + c)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True)
    a, b, c = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), c=c)

    Eq << Set.Le.of.In_Icc.apply(Eq[1])

    Eq << Set.Ge.of.In_Icc.apply(Eq[1])

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-02-26
