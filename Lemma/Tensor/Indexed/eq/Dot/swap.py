from util import *


@apply
def apply(x, d, w=None):
    n = x.shape[0]
    S[n], = d.shape
    i, j, k = Symbol(integer=True)

    if w is None:
        w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    return Equal(x[d @ w[i, j, k]], Stack[k:n](x[d[k]]) @ w[i, j, k])


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(complex=True, shape=(n,))
    d = Symbol(integer=True, shape=(n,))
    Eq << apply(x, d)

    k = Eq[-1].rhs.args[1].indices[-1]
    d = Eq[-1].lhs.indices[0].args[0]
    Eq << Eq[-1].rhs.this.subs(Eq[0][k]).this.rhs.apply(Tensor.Dot.eq.Sum)

    i, j, _ = Eq[-1].lhs.args[1].indices
    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].this(j).find(Element).simplify()

    Eq << Eq[-1].this(k).find(Element).simplify()

    Eq.eq = Eq[1].subs(Eq[-1])

    Eq << Eq.eq.lhs.indices[0].this.subs(Eq[0][k]).this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].this(j).find(Element).simplify()

    Eq << Eq[-1].this(k).find(Element).simplify()

    Eq << Eq.eq.subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-09-02
# updated on 2022-01-08
