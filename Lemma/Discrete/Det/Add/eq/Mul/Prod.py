from util import *


@apply
def apply(n, a):
    i = Symbol(integer=True)
    return Equal(Det(1 + a[:n] * Identity(n)), (1 + Sum[i:n](1 / a[i])) * Product[i:n](a[i]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Tensor, Finset, Nat

    n = Symbol(integer=True, positive=True, given=False)
    a = Symbol(shape=(oo,), complex=True, zero=False)
    Eq << apply(n, a)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.rhs.expand()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Discrete.Det.eq.Sum.expansion_by_minors.apply(Eq.induct.lhs, i=n)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Sum)().find(Add).simplify()

    Eq << Eq[-1].this.find(Stack)().expr.simplify()

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Eye)

    Eq.deduct = (Eq[-1] - Eq[-1].lhs.args[0]).subs(Eq[0])

    Eq << Eq.deduct.find(Product).this.apply(Finset.Prod.eq.MulProdS, cond={n})

    Eq << Eq.deduct.find(Mul, Sum).this.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq.deduct.rhs.this.subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Algebra.And.given.And.trans.apply(Eq.deduct & Eq[-1])

    Eq.deduction = Eq[-1].reversed

    D = Eq.deduction.lhs.expr.args[1].arg
    i = Eq.deduction.lhs.variable.copy(domain=Range(n))
    D = D._subs(Eq.deduction.lhs.variable, i)
    def column_transformation(*limits):
        n = limits[0][-1]
        (i, *_), (j, *_) = limits
    # return Identity(n) + Stack[j:n, i:n](Piecewise((0, i < n - 1), (KroneckerDelta(j, n - 1) - 1, True)))
    # return Identity(n) + Stack[j:n, i:n](Piecewise((KroneckerDelta(j, n - 1) - 1, Equal(i, n - 1)), (0, True)))
        return Identity(n) + Stack[j:n, i:n](KroneckerDelta(i, n - 1) * (KroneckerDelta(j, n - 1) - 1))
    # return Stack(Piecewise((KroneckerDelta(i, j), i < n - 1), (2 * KroneckerDelta(j, n - 1) - 1, True)), *limits)
    Eq << (D @ column_transformation(*D.limits)).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.eq.Add.pop)

    Eq.split = Eq[-1].this.rhs().find(Mul, Add, KroneckerDelta).simplify()

    Eq << Eq.split.find(Sum).this().find(Add[2]).simplify()

    Eq << Eq.split.find(Sum[2]).this().find(Add[2]).simplify()

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Nat.AddIteS.eq.IteAnd, swap=True)

    Eq << Eq.split.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Stack[~Add]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.find(Add, Piecewise).apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not)

    Eq << Eq[-1].this.find(Add, Stack)().find(NotElement).simplify()

    Eq << Eq[-1].this.find(Add, Piecewise).apply(Bool.Ite.subst, index=1)

    Eq << Eq[-1].this.find(Add, Stack)().find(ExprCondPair)().expr.simplify()

    Eq.column_transformation = Eq[-1].this.find(ExprCondPair[3])().expr.simplify()

    Eq << Discrete.Det.eq.Sum.expansion_by_minors.apply(Det(Eq.column_transformation.rhs), i=i).this.rhs.simplify(deep=True)

    Eq << Eq[-1].this.rhs.find(Stack)().find(Symbol < Add).simplify()

    Eq << Eq[-1].this.rhs.find(Stack)().find(Symbol < Add).simplify()

    Eq << Eq[-1].this.rhs.find(Add[Stack]).apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Add[Stack]).apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.find(ExprCondPair[~Stack])().find(Equal).simplify()

    Eq << Eq[-1].this.rhs.find(ExprCondPair[2]).find(Stack)().find(Equal).simplify()

    Eq << Eq[-1].this.rhs.find(Stack)().find(ExprCondPair)().expr().find(ExprCondPair[2])().find(KroneckerDelta).simplify()

    Eq << Eq[-1].this.rhs.find(Stack)().find(ExprCondPair[2])().expr().find(ExprCondPair)().find(KroneckerDelta).simplify()

    Eq << Eq[-1].this.find(Mul, Det).doit(deep=True)

    Eq << Eq[-1].this.find(Product[2]).apply(Algebra.Prod.limits.subst.offset, -1)

    k = Eq[-1].find(Product).variable
    Eq << Product[k:n](Eq[-1].find(Product).expr).this.apply(Finset.Prod.eq.MulProdS, cond={i})

    Eq.det_lamda = Eq[-2].subs((Eq[-1] / Eq[-1].rhs.args[0]).reversed)

    Eq << Eq.column_transformation.apply(Discrete.EqDet.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1].subs(Eq.det_lamda).apply(Bool.All.of.Cond, i)

    Eq << Algebra.And.given.And.subst.All_Eq.apply(Eq.deduction & Eq[-1])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
# created on 2020-10-04
# updated on 2023-05-12
