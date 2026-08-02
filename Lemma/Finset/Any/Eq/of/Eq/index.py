from util import *



@apply
def apply(given, j=None):
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Stack[k:a:a + n](arg).simplify()

    if j is None:
        j = Symbol(domain=Range(n))

    assert 0 <= j < n

    return Any[k:n](Equal(x[k], j))


@prove
def prove(Eq):
    from Lemma import Set

    n = Symbol(domain=Range(2, oo), given=True)
    x = Symbol(shape=(oo,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), j)

    Eq << ~Eq[-1]

    Eq << Eq[-1].reversed.this.expr.apply(Set.NotIn.of.Ne, simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.NotIn.Cup.of.NotIn, limit=(k, 0, n))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-23
