from util import *


@apply
def apply(eq, all):
    (w, i, j), (S[i], S[j]) = eq.of(Equal[Indexed, SwapMatrix])
    ((S[w[0, j]], x), s), (S[x], S[s]) = all.of(All[Element[MatMul]])

    return All[x:s](Element(w[i, j] @ x, s))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Set, Logic

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    w = Symbol(real=True, shape=(n, n, n, n))
    i, j = Symbol(integer=True)
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)), All[x:S](Element(w[0, j] @ x, S)))

    j_ = j.copy(domain=Range(n))
    Eq.given = Eq[1].subs(j, j_)

    i_ = i.copy(domain=Range(n))
    Eq.given_i = Eq.given.subs(j_, i_)

    Eq << Logic.Or_NotIn.of.All.apply(Eq.given, x, Eq.given_i.expr.lhs)

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[-1], Eq.given_i)

    Eq << Logic.All.of.All_And.apply(Eq[-1], index=-1)

    Eq << Logic.Or_NotIn.of.All.apply(Eq.given_i, x, Eq[-1].expr.lhs)

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[-2], Eq[-1])

    Eq << Logic.All.of.All_And.apply(Eq[-1], index=1)

    Eq.final_statement = Logic.AllIn.of.All.apply(Eq[-1], (i_,), (j_,))

    Eq << Discrete.All.Eq.of.Eq.Stack.SwapMatrix.swap2.Eq.apply(Eq[0])

    Eq << Eq[-1].this.expr @ x

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (Eq[-1].limits[0].args[1].args[1].arg,))

    Eq << Logic.All_And.of.All.All.apply(Eq.final_statement, Eq[-1])

    Eq.i_complement = Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst)

    Eq.plausible = All(Element(w[i, j] @ x, S), (x, S), (j, Range(1, n)), plausible=True)

    Eq << Algebra.All.given.And.All.apply(Eq.plausible, cond=i.set, wrt=j)

    Eq << Set.Inter.eq.Ite_.ExprCondPair_.Finset.In.ExprCondPairEmpty.apply(i, Range(1, n))

    Eq << Eq[-2].this.limits[1].subs(Eq[-1])



    Eq << Eq[-1].subs(Eq[0].subs(j, i)).simplify()

    Eq << Discrete.EqSwapMatrix.of.Eq.swap.apply(Eq[0]).subs(j, 0)

    Eq.given_i = Logic.AllIn.of.All.apply(Eq.given_i, (i_,))

    Eq << Eq.given_i.subs(Eq[-1].reversed)

    Eq << Algebra.All.given.And.All.apply(Eq[2], cond=Equal(j, 0))





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2023-08-26
