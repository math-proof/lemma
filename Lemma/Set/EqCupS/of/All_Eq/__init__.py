from util import *



@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(All[i:n](Equal(f(i), g(i))))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq.hypothesis, cond=Equal(f(n), g(n)))
    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)
    Eq << Eq[-1].this.rhs.apply(Set.EqCupSIn_Icc.of.EqCupSIn_Ico.Eq.Le)
    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2018-09-27

# updated on 2023-05-21
from . import fin
