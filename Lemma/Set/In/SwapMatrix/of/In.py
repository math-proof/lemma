from util import *


@apply
def apply(given, w=None):
    e, S = given.of(Element)
    x, i = e.args
    n = x.shape[0]
    j = Symbol(integer=True)
    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    return Element(w[i, j] @ x[:n], CartesianSpace(S, n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    Eq << apply(Element(x[i], S))

    Eq << Tensor.InDot.SwapMatrix.of.In.apply(Eq[0])

    k = Eq[-1].lhs.args[0].indices[-1]
    Eq << Bool.AllIn.of.All.apply(Eq[-1], (k, 0, n))

    Eq << Set.In_CartesianSpace.given.All.In.apply(Eq[2])





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-04
# updated on 2023-08-26
