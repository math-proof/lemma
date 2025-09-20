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

    return All[x:P](Element(x @ MatProduct[i:m](w[i, d[i]]), P))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Logic, Tensor

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, nonnegative=True, given=False)
    d = Symbol(shape=(n,), integer=True, nonnegative=True)
    Eq << apply(m, d)

    Eq.induct = Eq[-1].subs(m, m + 1)

    w, i, j = Eq[0].lhs.args
    Eq << Tensor.All_InDot.permutation.apply(n, w, left=False).subs(i, m).subs(j, d[m])

    Eq << Logic.Or_NotIn.of.All.apply(Eq[-1], Eq[-1].variable, Eq[2].expr.lhs)

    Eq << Eq[-1].this.args[0].lhs.simplify()

    Eq << Eq[-1].apply(Logic.AllIn.of.All, Eq[-3].limits[0])

    Eq <<= Eq[-1] & Eq[2]

    Eq << Logic.All.of.All_And.apply(Eq[-1], 1)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=m)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-02
# updated on 2023-05-20
