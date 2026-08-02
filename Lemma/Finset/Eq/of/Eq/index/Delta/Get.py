from util import *


@apply
def apply(given, i=None, j=None):
    (xk, (k, a, b)), n = given.of(Equal[Cup[FiniteSet], Range[0]])
    assert b - a == n

    x = Stack[k:a:b](xk).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    Eq << Eq[-1].apply(Bool.Cond.given.Or.OrNot, cond=Equal(i, j))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(Algebra.Ne.of.Eq.Ne.subst)

    Eq << Eq[-1].this.apply(Algebra.Cond.of.Ne.Cond.subst, ret=0)

    Eq << Eq[0].apply(Set.EqCard.of.Eq)

    Eq << Set.All.Ne.SDiff.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].lhs.index, j)

    Eq << Eq[-1].this.expr.reversed

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-24
