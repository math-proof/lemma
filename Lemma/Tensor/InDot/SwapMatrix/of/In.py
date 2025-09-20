from util import *


@apply
def apply(given, w=None, n=None):
    e, S = given.of(Element)
    x, i = e.args

    if n is None:
        n = x.shape[0]

    j = Symbol(integer=True)
    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix
    k = Symbol(integer=True)

    return Element(w[i, j, k] @ x[:n], S)


@prove
def prove(Eq):
    from Lemma import Set, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    Eq << apply(Element(x[i], S))

    i, j, k = Eq[-1].lhs.args[0].indices
    Eq << (Eq[1].lhs[k] @ x).this.args[0].definition

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].this(j).find(Element).simplify()

    Eq << Eq[-1].this(k).find(Element).simplify()

    Eq.element_piecewise = Eq[2].subs(Eq[-1])

    Eq <<= Eq[0].subs(i, j), Eq[0].subs(i, k)

    Eq << Set.Subset.Finset.of.In.In.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Set.Subset.of.In.Subset.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Set.In.Ite.of.Subset.apply(Eq[-1], piecewise=Eq.element_piecewise.lhs)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-04
# updated on 2022-01-08
