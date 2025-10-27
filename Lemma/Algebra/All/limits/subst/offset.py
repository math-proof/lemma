from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return limits_subs(All, self, index, offset, simplify=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    n, m, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), d)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Int.AllIn_Ico.of.AllIn_Ico.offset, d)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.All.limits.subst.offset, d)


if __name__ == '__main__':
    run()
# created on 2018-12-20
