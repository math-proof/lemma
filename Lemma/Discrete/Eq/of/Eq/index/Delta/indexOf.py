from util import *


@apply
def apply(given, i=None, j=None):
    from Lemma.Discrete.And.of.Eq.index import index_function
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Stack[k:a:a + n](arg).simplify()


    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    index = index_function(n)

    di = index[i](x[:n])
    dj = index[j](x[:n])

    return Equal(KroneckerDelta(di, dj), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Bool

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    j, i = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    Eq << Eq[-1].apply(Bool.Cond.given.Or.OrNot, cond=Equal(i, j))

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(Algebra.Ne.of.Eq.Ne.subst)

    Eq << Eq[-1].this.apply(Algebra.Cond.of.Ne.Cond.subst, ret=0)

    Eq << Discrete.And.of.Eq.index.apply(Eq[0], j=j)[1]

    Eq << Eq[-2].this.args[1].rhs.subs(Eq[-1].reversed)

    Eq << Discrete.And.of.Eq.index.apply(Eq[0], j=i)[1]

    Eq << Eq[-2].this.args[1].lhs.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebra.Ne.of.Eq.Ne.subst)





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-25
# updated on 2023-05-20
