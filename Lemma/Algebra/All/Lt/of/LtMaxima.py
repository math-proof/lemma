from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Maxima])
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, t = Symbol(real=True)
    M = Symbol(real=True, given=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Maxima[x:S](f(x)) < M)

    Eq << Algebra.Le.of.Lt.apply(Eq[0])

    Eq << Algebra.All.Le.of.LeMaxima.apply(Eq[-1])

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=Equal(S, S.etype.emptySet))

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Lt.given.And)

    Eq << Eq[-1].this.rhs.apply(Logic.All_And.given.All.All)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq.infer_is_empty = Eq[-2].this.apply(Logic.Imp.Is.ImpNotS)

    Eq << Eq[0].this.lhs.limits_subs(x, t)

    Eq << Algebra.All_Le_Maxima.apply(Eq[0].lhs)

    Eq << Eq[-1].limits_subs(t, x)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[-1], Eq.infer_is_empty)

    Eq << Eq[-1].this.lhs.apply(Logic.Any_And.of.Any.All.All_Imp)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Le.of.Eq.Le)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-12
