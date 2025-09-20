from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.Sum.limits.subst.Neg import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:a:b](f(i)), i, c - i)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.of.All.limits.subst.reverse, i, c - i)
    Eq << Eq[-1].this.lhs.apply(Algebra.All.of.All.limits.subst.reverse, i, c - i)


if __name__ == '__main__':
    run()
# created on 2018-06-20
