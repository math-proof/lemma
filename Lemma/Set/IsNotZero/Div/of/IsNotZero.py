from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert Element(0, domain) == False
    return Element(1 / x, Interval.open(0, oo) | Interval.open(-oo, 0))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo) | Interval.open(-oo, 0)))

    Eq << Set.OrInS.of.In_Union.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Set.IsNegative.Div.of.IsNegative)

    Eq << Eq[-1].this.args[0].apply(Set.IsPositive.Div.of.IsPositive)





if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-13
