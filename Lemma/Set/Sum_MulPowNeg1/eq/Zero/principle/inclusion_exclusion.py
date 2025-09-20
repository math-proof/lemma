from util import *


@apply
def apply(A):
    n = A.shape[0]
    i, j = Symbol(integer=True)
    d = Symbol(shape=(oo,), integer=True)
    k = Symbol(domain=Range(n + 1))
    M = Symbol(Stack[k](Piecewise((Sum[d[:k]:All[j:i, i:k](d[j] < d[i]):CartesianSpace(Range(n), k)](Card(Cap[i:k](A[d[i]]))), k > 0), (Card(Cup[i:n](A[i])), True))))

    assert M.shape[0] == n + 1
    return Equal(Sum[k]((-1) ** k * M[k]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo))
    A = Symbol(etype=dtype.integer, shape=(n,))
    Eq << apply(A)

    _k = Eq[-1].lhs.variable
    k = _k.unbounded
    Eq << Eq[-1].this.lhs.limits_subs(_k, k)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.domain_defined)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={0})

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[0].subs(_k, 0)

    Eq << Eq[-2].this.lhs.subs(Eq[-1]).reversed

    Eq << Eq[0].subs(_k, k)

    Eq << Logic.All.of.All_OrNot.apply(Eq[-1], 1)

    Eq << Eq[-3].this.lhs.subs(Eq[-1])

    Eq << Set.Sum_Sum_CardCap.eq.CardCup.principle.inclusion_exclusion.deduction.apply(A)


if __name__ == '__main__':
    run()


# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
# created on 2021-04-23
