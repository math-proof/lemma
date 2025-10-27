from util import *


@apply
def apply(n):
    i = Symbol(integer=True)

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    b = Symbol(integer=True, shape=(oo,), nonnegative=True)

    return All[p[:n]:P](Any[b[:n]](Equal(p[:n], Stack[i:n](i) @ MatProduct[i:n](SwapMatrix(n, i, b[i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Discrete, Bool, Tensor, Nat, Int

    n = Symbol(domain=Range(2, oo), given=False)
    Eq << apply(n)

    b = Eq[1].expr.variable.base
    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.doit(deep=True)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    Eq << Eq[-1].this.find(Sliced).apply(Algebra.Slice.eq.Matrix)

    p0 = Eq[-1].variable
    Eq << Eq[-1].this.expr.apply(Algebra.Any.given.Cond.subst, b[:2], Matrix((0, KroneckerDelta(p0, 0))))

    Eq << Eq[-1].this.expr.rhs.expand()

    Eq << Eq[-1].this.expr.rhs[0].simplify()

    Eq.equation = Eq[-1].this.expr.rhs[1].simplify()

    Eq.limits_assertion = Algebra.All.limits_assert.apply(Eq.equation.limits)

    Eq << Eq.limits_assertion.this.expr.apply(Set.Eq.of.Eq.split.Finset.Add)

    Eq.p1_equality = Eq[-1].this.expr - p0

    Eq <<= Eq.equation & Eq.p1_equality

    Eq << Eq[-1].this.expr.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.given.And.split.Matrix)

    Eq.premier, Eq.second = Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << Eq.limits_assertion.this.expr.apply(Set.And.of.Eq.split.Finset)

    Eq << Bool.All.All.of.All_And.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(Set.Eq.Delta.Zero.of.In).reversed

    Eq << -(Eq.premier - 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.expr.expr.rhs.args[1].this.apply(Tensor.MatProd.eq.Dot.pop)

    Eq << Discrete.Block.eq.MatProd.apply(n, n, b)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(Tensor.Stack.eq.Block.pop)

    Eq << MatMul(*Eq[-1].expr.expr.rhs.args[:2]).this.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.deduction = Eq[-1].this.expr.expr @ Eq[-1].expr.expr.rhs.args[1]

    Eq << Discrete.All_Any_Eq.permutation.basic.apply(n + 1)

    Eq << Eq[-1].this.expr.limits_subs(Eq[-1].expr.variable, b[n])

    Eq.any_n = Eq[-1].this.limits[0][1].definition

    p_quote = Symbol(Eq.deduction.expr.expr.lhs)
    Eq.p_quote_definition = p_quote.this.definition

    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)

    Eq << Eq.p_quote_definition.lhs[n].this.definition

    Eq << Eq[-1].this.rhs.args[1].expr.apply(Int.Ite.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Algebra.All.Any.of.All_Any_Eq.Cond.subst.apply(Eq.any_n, Eq[-1])

    Eq << Eq[-1].this.expr().expr.rhs.simplify()

    Eq.any_n_plausible = Eq[-1].this.expr.apply(Set.Any.of.Any.limits.relax, wrt=Eq[-1].expr.variable)

    Eq << Tensor.All_InDot.permutation.apply(n + 1, left=False)

    i, j = Eq[-1].find(Indexed).indices
    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.any_n_plausible.variable).subs(Eq.p_quote_definition.reversed)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.limits[0][1].definition

    Eq <<= Eq.any_n_plausible & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Bool.Any_And.of.Any.All)

    Eq << Eq[-1].this.expr.expr.apply(Discrete.Eq.of.Eq.Eq.permutation.pop.Icc)

    Eq << Bool.Or_NotIn.of.All.apply(Eq.hypothesis, Eq.hypothesis.variable, p_quote[:n])

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.of.Any.Or, simplify=None)

    Eq << Eq.p_quote_definition.lhs.this.apply(Algebra.Expr.eq.Block, n)

    Eq << Algebra.All.Any.And.of.Cond.All_Any.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(Bool.UFn.of.UFn.Eq, swap=True)

    Eq <<= Eq[-1] & Eq.any_n_plausible

    Eq << Eq[-1].this.expr.apply(Algebra.Any.And.of.Any.Any, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Bool.UFn.of.UFn.Eq, swap=True)

    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.limits.concat)
    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=2)

    Eq << Eq[1].subs(Eq[0])





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-01
# updated on 2023-11-18
