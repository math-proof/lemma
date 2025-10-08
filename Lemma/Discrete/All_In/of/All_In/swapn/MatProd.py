from util import *


@apply
def apply(given, m=None, b=None):
    ((x, (w, i, j)), s), (S[x], S[s]) = given.of(All[Element[MatMul[Indexed]]])

    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    if m is None:
        m = Symbol(integer=True, nonnegative=True)

    if b is None:
        b = Symbol(integer=True, shape=(oo,))

    return All[x:s](Element(x @ MatProduct[i:m](w[i, b[i]]), s))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Tensor

    n = Symbol(domain=Range(2, oo))
    m = Symbol(integer=True, nonnegative=True, given=False)
    S = Symbol(etype=dtype.integer[n], given=True)
    x = Symbol(shape=(n,), integer=True)
    i, j = Symbol(integer=True)
    w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))
    given = All[x[:n]:S](Element(x[:n] @ w[i, j], S))
    Eq.swap, Eq.w_definition, Eq.hypothesis = apply(given, m=m)

    i, _, m = Eq.hypothesis.expr.lhs.args[1].limits[0]
    b = Eq.hypothesis.expr.lhs.args[1].expr.indices[1].base
    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    Eq << Eq.induct.expr.lhs.args[1].this.apply(Tensor.MatProd.eq.Dot.pop)

    Eq << x @ Eq[-1]

    Eq << Eq.swap.subs(i, m).subs(j, b[m])

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], x, Eq[1].rhs.func(*Eq[1].rhs.args[:2]))

    Eq << Eq[-1].apply(Bool.AllIn.of.All, (x, S))

    Eq <<= Eq[-1] & Eq.hypothesis

    Eq << Bool.All.of.All_And.apply(Eq[-1], 1)

    Eq << Eq[-1].subs(Eq[1].reversed)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=m)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-03
# updated on 2023-05-20
