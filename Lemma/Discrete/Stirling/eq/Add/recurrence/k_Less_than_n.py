from util import *


@apply
def apply(n, k):
    assert k < n
    return Equal(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    from Lemma import Discrete, Set, Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n))
    Eq << apply(n, k)

    Eq.Stirling2 = Eq[0].lhs.this.apply(Discrete.Stirling.eq.Card)

    Eq.Stirling0 = Eq[0].rhs.args[1].this.apply(Discrete.Stirling.eq.Card)

    Eq.Stirling1 = Eq[0].rhs.args[0].args[1].this.apply(Discrete.Stirling.eq.Card)

    s2 = Symbol(Eq.Stirling2.rhs.arg)
    Eq << s2.this.definition

    Eq.Stirling2 = Eq.Stirling2.subs(Eq[-1].reversed)

    s0 = Symbol(Eq.Stirling0.rhs.arg)
    Eq << s0.this.definition

    Eq.Stirling0 = Eq.Stirling0.subs(Eq[-1].reversed)

    s1 = Symbol(Eq.Stirling1.rhs.arg)
    Eq << s1.this.definition

    Eq.Stirling1 = Eq.Stirling1.subs(Eq[-1].reversed)

    e = Symbol(etype=dtype.integer.set)
    Eq << Set.Eq_Union_.Inter.SDiff.apply(s2, conditionset(e, Element({n}, e), s2))

    Eq.s2_abs = Eq[-1].apply(Set.EqCard.of.Eq)

    Eq.s2_abs_plausible = Eq[0].subs(Eq.Stirling2, Eq.Stirling0, Eq.Stirling1)

    Eq << Discrete.Condset.eq.Cup.Stirling.mapping.s2_A.apply(n, k, s2)

    A = Eq[-1].rhs.expr.base
    Eq << Discrete.Condset.Stirling.mapping.s2_B.apply(n, k, s2)

    B = Eq[-1].rhs
    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq << Discrete.Abs.Imageset.Stirling.mapping.s0_B.apply(n, k, s0, B)

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1]) - Card(s0)

    Eq << Discrete.Abs.Cup.eq.Sum.Stirling.nonoverlapping.A.apply(n, k, A)

    Eq << Eq.A_union_abs.subs(Eq[-1])

    Eq << Discrete.Abs.Condset.Stirling.mapping.s1_Aj.apply(n, k, s1, A).reversed

    Eq << Eq[-1].apply(Algebra.EqSumS.of.Eq, *Eq[-2].lhs.limits)


if __name__ == '__main__':
    run()

# created on 2020-10-06
