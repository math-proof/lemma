from util import *


@apply
def apply(self, old, new):
    from Lemma.Algebra.All.limits.subst.Neg.real import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Int

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[0], simplify=None)

    Eq << Int.Any_UFnNeg.of.Any.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Set.Neg.In.Icc.of.In_Icc)

    Eq << Int.AnyIn_Ico.of.AnyIn_Ico.offset.apply(Eq[-1], -c)


if __name__ == '__main__':
    run()
# created on 2019-02-17
