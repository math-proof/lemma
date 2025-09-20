from util import *


@apply
def apply(n, w=None, left=True, P=None):
    i, j = Symbol(integer=True)

    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]

    if P is None:
        P = Symbol(conditionset(x, Equal(x.cup_finiteset(), Range(n))))

    if left:
        return All[x:P](Element(w[i, j] @ x, P))
    else:
        return All[x:P](Element(x @ w[i, j], P))


@prove
def prove(Eq):
    from Lemma import Discrete
    n = Symbol(domain=Range(2, oo))

    Eq << apply(n)

    w = Eq[0].lhs.base

    x = Eq[2].variable

    Eq << Discrete.Cup.Finset.rmatmul.apply(x, w)

    Eq << Eq[2].this.expr.rhs.definition.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-07-26
