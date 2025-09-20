from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.All.limits.subst.Neg.real import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, right_open=True)](f(x) > 0), x, c - x)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.subst.Neg.real, x, c - x)
    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Any.limits.subst.Neg.real, x, c - x)


if __name__ == '__main__':
    run()
# created on 2019-02-20
