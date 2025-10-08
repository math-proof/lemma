from util import *


@apply
def apply(given):
    (fx, A), *limits = given.of(All[Subset])

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from Lemma import Bool, Set

    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])
    Eq << apply(All[i:m](Subset(x[i], A)))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(m, 1)

    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq.hypothesis, cond=Subset(x[m], A))

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], m, start=1)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()

# created on 2018-04-19
# updated on 2023-05-21
