from util import *


def index_function(n):
    k = Symbol(integer=True)

    def eval(*args):
        if len(args) == 3:
            x, a, (j,) = args
            j = a[j]
        else:
            x, (j,) = args

        return Stack[k:n](KroneckerDelta(x[k], j)) @ Stack[k:n](k)

    index = Function(shape=(), integer=True)
    index.eval = eval
    return index


@apply
def apply(given, j=None):
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Stack[k:a:a + n](arg).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n

    index = index_function(n)
    index_j = index[j](x[:n], evaluate=False)
#     index_j = index[j](x[:n])
    return Element(index_j, Range(n)), Equal(x[index_j], j)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo))

    x = Symbol(shape=(oo,), integer=True)

    k = Symbol(integer=True)

    j = Symbol(domain=Range(n), given=True)

    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), j)

    a = Symbol(Stack[k:n](k))
    Eq.aj_definition = a.this.definition[j]

    Eq << a.cup_finiteset().this.expr.arg.base.definition

    Eq << Eq[-1].apply(Set.EqCard.of.Eq)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[0], Eq[-2])

    Eq << Discrete.And.of.Eq.Eq.index_general.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-2].this.lhs.defun(), Eq[-1].this.lhs.indices[0].defun()

    Eq <<= Eq[-2].subs(Eq.aj_definition), Eq[-1].subs(Eq.aj_definition)

    Eq << Eq[1].this.lhs.defun()

    Eq << Eq[2].this.lhs.indices[0].defun()


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-07-22
