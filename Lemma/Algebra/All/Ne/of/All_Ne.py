from util import *


@apply
def apply(all_ne):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_ne.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi
    x = Stack[i:n](xi).simplify()
    assert xj == x[j]

    return All[j:Range(n) - {i}, i:n](Unequal(xi, xj))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    i, j = Symbol(integer=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])))

    k = Symbol(integer=True)
    Eq << Eq[0].limits_subs(j, k).limits_subs(i, j).limits_subs(k, i)

    Eq << Eq[-1].this.apply(Algebra.All.limits.swap.intlimit)

    Eq << Eq[-1].this.expr.reversed

    Eq << Bool.AllOr.of.All.All.apply(Eq[-1], Eq[0])

    Eq << Bool.Or_Not.of.All.apply(Eq[-1])

    Eq << Bool.ImpNot.of.Or.apply(Eq[-1], 1)

    Eq << Element(i, Range(-1, n + 1)).this.apply(Set.Union.eq.SDiff.of.In_Ico)

    Eq << Eq[-1].this.lhs.apply(Set.In.given.In.restrict, Range(0, n))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Bool.All.of.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Bool.All.of.All_OrNot, 1)





if __name__ == '__main__':
    run()
# created on 2022-01-24
# updated on 2023-05-19
