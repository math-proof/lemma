from util import *


@apply
def apply(m, d, w=None, x=None):
    n = d.shape[0]
    i, j = Symbol(integer=True)

    assert m >= 0
    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    if x is None:
        x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]

    P = Symbol(conditionset(x, Equal(x.cup_finiteset(), Range(n))))

    return Element(Stack[i:n](i) @ MatProduct[i:m](w[i, d[i]]), P)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool
    n = Symbol(domain=Range(2, oo), given=True)
    m = Symbol(integer=True, nonnegative=True)
    d = Symbol(shape=(n,), integer=True, nonnegative=True)
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)

    Eq << apply(m, d, x=x)

    Eq << Discrete.All_In_MatProd.permutation.apply(m, d, x=x)

    Eq.ou = Bool.Or_NotIn.of.All.apply(Eq[-1], Eq[-1].variable, Eq[2].lhs.args[0])

    Eq << Any[x](Eq.ou.args[1], plausible=True)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.lhs.simplify()

    Eq << ~Eq[-2]

    Eq << Eq[-1].simplify()

    Eq <<= Eq.ou & Eq[-1]

    Eq << Bool.Cond.of.And.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-11-05
