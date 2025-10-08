from util import *


@apply
def apply(a_size, xa_equality, j=None):
    x_cup_finiteset, a_cup_finiteset = xa_equality.of(Equal)
    xexpr, (k, a, b) = x_cup_finiteset.of(Cup[FiniteSet])
    S[a_cup_finiteset], n = a_size.of(Equal[Card])

    assert n == b - a

    aexpr, (_k, _a, _b) = a_cup_finiteset.of(Cup[FiniteSet])
    assert n == _b - _a

    x = Stack[k:a:b](xexpr).simplify()
    a = Stack[_k:_a:_b](aexpr).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n

    from Lemma.Discrete.And.of.Eq.index import index_function
    index = index_function(n)
    index_j = index[j](x[:n], a[:n], evaluate=False)
    return Element(index_j, Range(n)), Equal(x[index_j], a[j])


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool, Tensor

    n = Symbol(domain=Range(2, oo), given=True)
    x, a = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(Card(a.cup_finiteset(k)), n),
                Equal(x[:n].cup_finiteset(k), a.cup_finiteset(k)),
                j=j)

    Eq << Eq[2].lhs.this.defun()

    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.indices[0].this.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].rhs.expr.args[1].this.apply(Algebra.Delta.eq.Ite)

    Eq << Algebra.Eq.of.Eq.Eq.subst.rhs.apply(Eq[-1], Eq[-2])

    s_j = Symbol(conditionset(k, Equal(a[j], x[k]), Range(n)))
    Eq.s_j_definition = s_j.this.definition

    Eq << Sum[k:s_j](k).this.limits[0][1].definition

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={0})

    Eq.crossproduct = Bool.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])

    Eq.s_j_definition_reversed = Eq.s_j_definition.this.rhs.limits[0][1].reversed.reversed

    Eq << Eq[1].apply(Set.EqInter.of.Eq, {a[j]})

    k_ = Eq[-1].find(Cup).variable
    Eq << Piecewise((x[k_].set, Equal(x[k_], a[j])), (x[k_].emptySet, True)).this.simplify()

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1].reversed, (k_, 0, n))

    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed

    Eq << Eq.distribute.this.lhs.apply(Set.Imageset.inner_subs)

    Eq << Eq[-1].subs(Eq.s_j_definition_reversed)

    Eq.s_j_greater_than_1 = Set.Ge.of.Ne_Empty.apply(Eq[-1])

    Eq.distribute = Eq.distribute.subs(Eq.s_j_definition_reversed)

    Eq.ou = Set.Card.le.One.ou.Any_Ne.apply(Eq.s_j_greater_than_1.lhs.arg)

    Eq.s_j_less_than_1 = Eq.ou.args[0].copy(plausible=True)

    Eq.inequality_ab = Eq.ou.args[1].copy(plausible=True)

    (a, *_), (b, *_) = Eq.inequality_ab.limits
    Eq << Eq[1].apply(Set.EqCard.of.Eq)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[0])

    Eq << Set.All.Ne.SDiff.of.Eq.apply(Eq[-1], exclude=a)

    Eq << Eq[-1].subs(k_, a)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], Eq[-1].variable, b)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.inequality_ab)

    Eq.distribute_ab = Eq[-1].this.expr.apply(Bool.OrAndS.of.And_Or)

    Eq.j_equality = Set.All_CupFinset.eq.Ico.apply(s_j)

    Eq << Eq.j_equality.limits_subs(k, a)

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq.j_equality.reversed, Eq.distribute_ab)

    Eq << Eq[-1].this.expr.args[::2].apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Eq[-1].this.expr.apply(Algebra.And.of.And.delete)

    Eq << Eq.j_equality.limits_subs(a, b)

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq.j_equality, Eq[-1])

    Eq <<= Eq.ou & ~Eq.inequality_ab

    Eq << Bool.Cond.of.And.apply(Eq[-1], index=0)

    Eq <<= Eq.s_j_less_than_1 & Eq.s_j_greater_than_1

    Eq << Set.In.Sum.of.Eq.apply(Eq[-1], var=k)

    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)

    Eq.ou = Bool.Or_NotIn.of.All.apply(Eq.j_equality, Eq.j_equality.variable, Eq.index_domain.lhs)

    Eq <<= Eq.ou.args[1].copy(plausible=True), Eq.ou.args[0].copy(plausible=True)

    Eq <<= Eq[-2] & Eq.index_domain

    Eq <<= Eq.ou & ~Eq[-2]

    Eq << Bool.Cond.of.And.apply(Eq[-1], index=0)

    Eq << Eq[-2].reversed

    Eq << Subset(s_j, Eq[2].rhs, plausible=True)

    Eq << Set.In.of.In.Subset.apply(Eq.index_domain, Eq[-1])





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-07-22
# updated on 2023-11-11

