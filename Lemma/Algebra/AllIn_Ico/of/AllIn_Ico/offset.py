from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return limits_subs(All, self, index, offset)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), 1)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[0], n, n + 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInSub.of.NotIn_Icc, 1)

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()
# created on 2018-07-11
