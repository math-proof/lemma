from util import *


@apply
def apply(eq_w):
    (w, i, j), (S[i], S[j]) = eq_w.of(Equal[Indexed, SwapMatrix])
    n = w.shape[-1]
    domain = Range(n)
    t = Symbol(domain=domain)
    assert n >= 2
    return All(Equal(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Logic, Tensor

    n = Symbol(domain=Range(2, oo))
    w = Symbol(integer=True, shape=(n, n, n, n))
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    t = Eq[1].expr.lhs.args[0].indices[0]
    p = Symbol(complex=True, zero=False)
    x = Stack[i:n](p ** i)
    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << (w[t, j] @ Eq[-1]).this.rhs.subs(Eq[0].subs(i, t))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs().expr.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.rhs().expr.args[2].cond.simplify()

    Eq << Eq[-1].this.rhs.expr.args[2].cond.apply(Set.In.Is.Or.split.Finset)

    Eq << Eq[-1].this.rhs().expr.apply(Logic.Ite__Ite.eq.Ite__IteAnd_Not, 1)

    Eq << Eq[-1].this.rhs.expr.apply(Logic.Ite.subst, index=2)

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (j,))

    Eq << Logic.AllIn.of.All.apply(Eq[-1], Eq[1].limits[0])

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq[-1].this.expr.apply(Discrete.Eq.of.Eq.rmatmul, w[t, i])

    Eq << Eq[-1].this.expr.rhs.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.expr.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this().expr.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this().expr.rhs().expr.args[-1].expr.args[1].apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.expr.rhs.expr.apply(Algebra.Ite.eq.AddMulS)

    Eq.www_expansion = Eq[-1].this().expr.rhs.expr.simplify()

    Eq << Algebra.All.of.Cond.domain_defined.apply(Eq[0], j)

    Eq << Eq[-1].simplify()

    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(Eq[-1]).this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)
    Eq << Eq[-1].this(j).rhs().expr.simplify(wrt=True)
    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Ite.eq.AddMulS)
    Eq << Eq.www_expansion.subs(Eq[-1].reversed)
    Eq << Eq[-1].this.expr.apply(Tensor.Eq.of.EqDotS_Stack_Pow.independence.matrix)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-23
# updated on 2023-05-21
