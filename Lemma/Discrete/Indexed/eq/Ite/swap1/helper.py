from util import *


@apply
def apply(x, w=None):
    n = x.shape[0]
    i, j = Symbol(integer=True)

    if w is None:
        w = Symbol(Stack[j](SwapMatrix(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == SwapMatrix(n, 0, j)

    return Equal(Stack[i:n](x[w[j][i] @ Stack[i:n](i)]), Stack[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Logic, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(etype=dtype.integer, shape=(n,))
    Eq << apply(x)

    w = Eq[0].lhs.base
    Eq << Discrete.Indexed.eq.Ite.swap1.apply(x, w)

    i, j = Eq[-1].rhs.args[0][1].args
    Eq << Eq[-1].apply(Logic.AllIn.of.All, (i,), (j,))

    _i = i.unbounded
    Eq << Eq[-1].this.find(Stack).limits_subs(i, _i)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (_i, 0, n), simplify=False)


if __name__ == '__main__':
    run()
# created on 2020-09-12
