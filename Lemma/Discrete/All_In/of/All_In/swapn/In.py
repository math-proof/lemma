from util import *


@apply
def apply(given):
    (((x, ((w, i, j, k), (S[k], (S[k], S[0], n)))), (S[k], S[0], S[n])), s), (S[x], S[s]) = given.of(All[Element[Stack[Indexed[MatMul[Indexed, Stack]]]]])
    [S[n]] = s.etype.shape

    (S[i], S[j]), (S[j], *j_limits), (S[i], *i_limits) = w.definition.of(Stack[SwapMatrix])

    if j_limits:
        S[0], S[n - 1] = j_limits

    if i_limits:
        S[0], S[n - 1] = i_limits

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    return All[p[:n]:P, x:s](Element(Stack[k:n](x[p[k]]), s))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    i, j, k = Symbol(integer=True)
    w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    Eq.swap, (Eq.P_definition, Eq.w_definition), Eq.axiom = apply(All[x:S](Element(Stack[k:n](x[(w[i, j] @ Stack[k:n](k))[k]]), S)))

    Eq << Tensor.Stack.Indexed.eq.Dot.swap.apply(x, w)

    Eq << Eq.swap.subs(Eq[-1])

    Eq << Discrete.All_In.of.All_In.swapn.permutation.apply(Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-04
