from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Subset])
    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(All[i:n](Subset(f(i), g(i))))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Logic.ImpAndS.of.Imp.apply(Eq.hypothesis, cond=Subset(f(n), g(n)))

    Eq << Eq[-1].this.rhs.apply(Set.Subset.Cup.of.Subset.Subset.push)
    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)
    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2020-08-03
# updated on 2023-05-21
