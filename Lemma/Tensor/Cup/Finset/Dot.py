from util import *


@apply
def apply(a, var=None, *, simplify=True):
    matmul = a.definition
    lhs, rhs = matmul.of(MatMul)

    if lhs.is_SwapMatrix:
        w = lhs
        x = rhs
    elif rhs.is_SwapMatrix:
        w = rhs
        x = lhs
    else:
        return
    a = a.cup_finiteset(var=var)
    x = x.cup_finiteset(var=var)
    if simplify:
        a = a.simplify()
        x = x.simplify()
    return Equal(a, x)


@prove
def prove(Eq):
    from Lemma import Discrete, Set

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    i, j, k = Symbol(integer=True)
    a = Symbol(x @ SwapMatrix(n, i, j))
    Eq << apply(a, var=k)

    w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    Eq << w[i, j].this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Discrete.Cup.Finset.rmatmul.apply(x, w, right=True, var=k)

    Eq << Eq[-2][k]

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.limits.domain_defined.delete)

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.domain_defined.delete)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-30
