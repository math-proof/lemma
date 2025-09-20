from util import *


@apply
def apply(given):
    ((((x0, condition0), (xj, conditionj), (xi, conditioni)), (i, S[0], n)), s), (j, S[1], S[n]), (x, S[s]) = given.of(All[Element[Stack[Piecewise]]])
    dtype = s.etype

    assert {*condition0.of(Equal)} == {i, j}
    assert {*conditionj.of(Equal)} == {i, 0}
    assert conditioni

    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type

    w = Symbol(Stack[j, i](SwapMatrix(n, i, j)))

    return All(Element(w[i, j] @ x, s), (x, s))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Logic

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    i, j = Symbol(integer=True)
    Eq << apply(All(Element(Stack[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))), S), (j, 1, n), (x, S)))

    w = Eq[1].lhs.base
    Eq << Discrete.Indexed.eq.Ite.swap1.helper.apply(x, w[0])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n), simplify=False)

    Eq.given = Eq[0].subs(Eq[-1].reversed)

    Eq << Tensor.Stack.Indexed.eq.Dot.swap.apply(x, w)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].indices[0], 0)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, i)

    Eq << Eq[-1].this.lhs.expr.indices[0].args[1].limits_subs(Eq[-1].lhs.expr.indices[0].args[1].variable, i)

    Eq.given = Eq.given.subs(Eq[-1])

    Eq << Algebra.All.of.All.limits.swap.apply(Eq.given)

    Eq << All[x:S](Eq[-1].expr._subs(j, 0), plausible=True)

    Eq << Eq[-1].subs(w[0, 0].this.definition)

    Eq << Eq[-1].simplify()

    Eq << Logic.All_And.of.All.All.apply(Eq[-2], Eq[-3])

    Eq << Discrete.All_In.of.Eq.All_In.swap2.apply(Eq[1], Eq[-1])




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-12
# updated on 2023-05-21
