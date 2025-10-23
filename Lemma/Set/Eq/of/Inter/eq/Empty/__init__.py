from util import *


@apply
def apply(given):
    A, B = given.of(Equal[Intersection, EmptySet])
    return Equal(Card(Union(A, B)), Card(A) + Card(B))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat, Finset

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet))

    Eq << Set.Sum_BoolIn.eq.Card.apply(A | B).reversed

    Eq << Set.EqBool.of.Eq_Empty.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.as_Plus = Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq <<= Eq.as_Plus.rhs.args[0].this.apply(Finset.Sum.eq.AddSumS, cond=A), Eq.as_Plus.rhs.args[1].this.apply(Finset.Sum.eq.AddSumS, cond=B)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1] + Eq.as_Plus

    Eq << Eq[-1].this.apply(Nat.EqAddS.Is.Eq)

    Eq << Set.Sum_BoolIn.eq.Card.apply(A)

    Eq << Set.Sum_BoolIn.eq.Card.apply(B)

    Eq << Eq[-1] + Eq[-2] + Eq[-3]

    Eq << Eq[-1].this.apply(Nat.EqAddS.Is.Eq)


if __name__ == '__main__':
    run()

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
# created on 2020-07-05


from . import Eq_SDiff
