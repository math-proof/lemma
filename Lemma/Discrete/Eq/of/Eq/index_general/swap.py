from util import *


@apply
def apply(given, i=None, j=None, w=None):
    from Lemma.Discrete.And.of.Eq.index import index_function
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Stack[k:a:a + n](arg).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    index = index_function(n)
    if w is None:
        _i = Symbol("i", integer=True)
        _j = Symbol("j", integer=True)
        w = Symbol(Stack[_j, _i](SwapMatrix(n, _i, _j)))

    return Equal(index[i](w[index[i](x[:n]), index[j](x[:n])] @ x[:n]), index[j](x[:n]))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Logic, Tensor

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True)
    k = Symbol(integer=True)
    j, i = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    _, di, dj = Eq[2].lhs.arg.args[0].args
    dj = Symbol("d_j", dj)
    di = Symbol("d_i", di)
    Eq.dj_definition = dj.this.definition

    Eq.di_definition = di.this.definition

    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)

    _i, _j = Eq[1].lhs.indices
    Eq << Eq[1].subs(_i, di).subs(_j, dj)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.definition = Eq[-1].this.lhs.defun()

    Eq.expand = Eq.definition.lhs.args[0].expr.args[1].this.apply(Tensor.Dot.eq.Sum)

    Eq << Discrete.And.of.Eq.index.apply(Eq[0], j=j)

    Eq.dj_domain, Eq.x_dj_eqaulity = Eq[-2].subs(Eq.dj_definition.reversed), Eq[-1].subs(Eq.dj_definition.reversed)

    Eq.expand = Eq.expand.subs(Eq.x_dj_eqaulity)

    Eq << Discrete.And.of.Eq.index.apply(Eq[0], j=i)

    Eq.di_domain, Eq.x_di_eqaulity = Eq[-2].subs(Eq.di_definition.reversed), Eq[-1].subs(Eq.di_definition.reversed)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq.di_domain, Eq.expand)

    Eq.expand = Logic.BFn.of.BFnIte.Cond.apply(Eq.dj_domain, Eq[-1])

    Eq << Set.Subset.Finset.of.In.In.apply(Eq.dj_domain, Eq.di_domain, simplify=False)

    Eq.eq_intersection = Set.EqInter.of.Subset.apply(Eq[-1])

    Eq << Eq.expand.subs(Eq.x_di_eqaulity)

    Eq.union_equality, Eq.piecewise_equality = Set.EqUnion.of.Subset.apply(Eq[-2]), Eq.definition.subs(Eq[-1])

    Eq.piecewise_equality = Eq.piecewise_equality.this.lhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq.piecewise_equality.lhs.args[-1].this.apply(Algebra.Sum.SDiff.eq.Add)

    Eq << Eq[-1].subs(Eq.eq_intersection)

    Eq << Eq[-1].subs(Eq.x_dj_eqaulity).subs(Eq.x_di_eqaulity)

    Eq << Eq[-1].this.rhs.subs(Eq.union_equality)

    Eq << Eq.di_definition.this.rhs.defun().this.rhs.apply(Tensor.Dot.eq.Sum)
    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq.piecewise_equality = Eq.piecewise_equality.subs(Eq[-1])

    Eq.dj_eq = Set.Eq_Ite.of.In.expr_swap.apply(Eq.dj_domain, Eq.piecewise_equality.lhs.args[2])

    Eq << Set.Eq_Ite.of.In.expr_swap.apply(Eq.di_domain, Eq.piecewise_equality.lhs.args[-1])

    Eq << Set.EqInter.of.In.apply(Eq.dj_domain)

    Eq << Logic.UFn.of.UFn.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.find(Element).simplify()

    Eq << Eq.dj_eq + Eq[-1]

    Eq << Eq.piecewise_equality.subs(Eq[-1])

    Eq << Discrete.Eq.of.Eq.index.Delta.indexOf.apply(Eq[0], i, j)

    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)

    Eq << Eq[-3].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-28
# updated on 2023-05-05
