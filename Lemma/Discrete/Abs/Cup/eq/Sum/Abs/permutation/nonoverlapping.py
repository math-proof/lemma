from util import *


@apply
def apply(n, Q=None):
    if Q is None:
        from Lemma.Discrete.All_And.mapping.Qu2v import predefined_symbols
        Q, w, x = predefined_symbols(n)

    t = Q.definition.variable
    return Equal(Card(Cup[t](Q[t])), Sum[t](Card(Q[t])))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    Q = Eq[0].lhs.base
    t = Q.definition.variable
    j = Symbol(integer=True)
    Eq.nonoverlapping = All[j: Range(n + 1) - {t}, t](Equal(Q[t] & Q[j], Q[t].etype.emptySet), plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.expr.apply(Set.Any_In.of.Inter.ne.Empty, wrt=Eq[0].rhs.variable, simplify=None)

    Eq << Eq[-1].this.find(Element).rhs.definition

    Eq << Bool.Any.of.Any_And.apply(Eq[-1], index=1)

    Eq << Set.All_CupFinset.eq.Ico.apply(Q[t])

    Eq << Bool.All.of.All_And.apply(Eq[-1], index=0)

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[-3])

    Eq << Set.Eq.of.All_Eq_Empty.nonoverlapping.setlimit.apply(Eq.nonoverlapping)




if __name__ == '__main__':
    run()
# created on 2020-08-06
# updated on 2023-05-20
