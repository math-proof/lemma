from util import *


@apply
def apply(eq, x):
    (i, j), wij = eq.of(Equal[ShiftMatrix])
    n, = x.shape
    return Equal(x @ wij @ wij.T, x)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    w = Symbol(shape=(n, n, n, n), real=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], ShiftMatrix(n, i, j)), x)

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    Eq << (x @ w[i, j]).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(Element[Symbol, Range[0]]).simplify()

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    #\.et\w*\.(to|given)
    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).find(And).apply(Set.Ne.NotIn.Is.NotIn)

    Eq << Eq[-1].this.rhs().expr.args[1].find(NotElement).apply(Set.NotIn.Is.In.SDiff)

    Eq << Eq[-1].this.rhs().expr.args[1].find(NotElement).apply(Set.NotIn.Is.In.SDiff)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 0)

    Eq << (Eq[-1] @ w[i, j].T).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.args[1].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.args[2].expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(Bool.Ite.eq.Ite__IteOr)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(Bool.Ite.subst, reverse=True)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify()





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-14
# updated on 2023-05-26
