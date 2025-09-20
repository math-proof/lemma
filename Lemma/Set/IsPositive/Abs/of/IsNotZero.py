from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Element(abs(x), Interval.open(0, oo))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Set.OrInS.of.In_Union.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0].apply(Set.IsPositive.Abs.of.IsPositive, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Set.IsPositive.Abs.of.IsNegative, simplify=None)





if __name__ == '__main__':
    run()
# created on 2020-04-16
# updated on 2023-05-12
