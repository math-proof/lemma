from util import *


@apply
def apply(boole):
    assert boole.is_Bool
    return Element(boole, {0, 1}, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, y = Symbol(real=True)
    Eq << apply(Bool(x > y))

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)

    S = Symbol(Eq[1].rhs)
    Eq << Or(Element(1, S) & (x > y), Element(0, S) & (x <= y), plausible=True)

    Eq << Eq[-1].this.find(Element[~Symbol]).definition

    Eq << Eq[-1].this.find(Element[~Symbol]).definition

    Eq << Set.InIte__Ite.of.And.ou.OrAndS.apply(Eq[-2], wrt=S)

    Eq << Eq[-1].this.rhs.definition

    Eq << Logic.Ite__Ite.eq.IteAnd_Not__Ite.apply(Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-03-08
# updated on 2023-06-18
