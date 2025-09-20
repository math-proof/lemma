from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    R = Interval.open(0, oo)
    assert domain in R
    return Element(1 / x, R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Set.Any.Eq.of.In.apply(Eq[0])

    Eq << Logic.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Div.gt.Zero.of.Gt_0)

    Eq << Eq[-1].this.find(Greater).apply(Set.IsPositive.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-03
