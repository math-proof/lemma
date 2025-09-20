from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.All.limits.subst.Neg.real import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Logic.Or_NotIn.of.All.apply(Eq[0], x, c - x)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn.Neg.of.NotIn)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotInAdd.of.NotIn, c)

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1], pivot=1, wrt=x)





if __name__ == '__main__':
    run()
# created on 2018-12-15
# updated on 2023-05-13
