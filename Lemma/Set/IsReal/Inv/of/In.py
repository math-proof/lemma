from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R == Reals - {0}

    return Element(1 / x, Reals)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << Set.OrInS.of.In_Union.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[1].apply(Set.In.Inv.Icc.of.In, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Set.In.Inv.Icc.of.In, simplify=False)

    Eq << Subset(Eq[-1].rhs, Eq[1].rhs, plausible=True)

    Eq << Set.In.of.In.Subset.apply(Eq[-2], Eq[-1], simplify=None)





if __name__ == '__main__':
    run()
# created on 2020-06-21
# updated on 2023-05-12
