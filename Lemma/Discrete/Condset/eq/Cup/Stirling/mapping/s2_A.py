from util import *


@apply
def apply(n, k, s2=None, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    j = Symbol(domain=Range(k + 1))
    if s2 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s2 = Symbol(Cup[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].cup_finiteset().set))

    e = Symbol(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol(Stack[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Stack[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))

    return Equal(conditionset(e, NotElement({n}, e), s2), Cup[j](A[j]))


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    k = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s2_quote = Symbol('s_quote_2', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition

    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    s1_quote = Eq[2].lhs
    Eq << Set.All_CupFinset.eq.Ico.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base
    Eq.x_abs_positive_s1 = Bool.All.of.All_And.apply(Eq[-1])

    Eq.x_abs_sum_s1 = Bool.All.of.All_And.apply(Eq[-1], 1)

    Eq.x_union_s1 = Bool.All.of.All_And.apply(Eq[-1], 2)

    j = Symbol(domain=Range(k + 1))
    x_quote = Eq[1].lhs.base
    Eq.x_quote_set_in_s2 = Subset(imageset(x_slice, Cup[i:k + 1](x_quote[i].set), s1_quote), Eq[0].lhs, plausible=True)

    Eq << Set.Subset.given.All_In.apply(Eq.x_quote_set_in_s2)

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].this.expr.apply(Set.In.given.In.split.Imageset)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[1], (i, 0, k + 1))

    Eq.x_quote_union = Algebra.All.of.All_Eq.Cond.subst.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[1].apply(Set.EqCard.of.Eq)

    x_quote_abs = Eq[-1]
    Eq << Eq[-1].apply(Algebra.EqSumS.of.Eq, (i, 0, k + 1))

    Eq << Set.CardUnion.le.AddCardS.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Algebra.Le.of.Eq.Le.subst.apply(Eq[-2], Eq[-1])

    Eq << Algebra.All.of.All_Eq.Cond.subst.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.expr.apply(Set.EqCard.of.Eq)

    x_quote_union_abs = Eq[-1]
    u = Eq[-1].lhs.arg
    Eq << Set.CardCup.le.Sum_Card.apply(u.expr, *u.limits)

    Eq << Eq[-2].this.expr.apply(Algebra.Ge.of.Eq.Le.subst, Eq[-1])

    Eq.SqueezeTheorem = Eq[-4] & Eq[-1]

    Eq << Bool.OrAndS.of.BFn_Ite.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << Eq[-2].apply(Bool.AllIn.of.All, (i, Unequal(i, j)))

    Eq << Set.CardUnion.ge.Card.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.expr.apply(Algebra.Gt.of.Gt.Ge, Eq[-1])

    Eq.xj_is_positive = Eq[-1].subs(Eq[-4].reversed)

    Eq << Bool.All_And.of.All.All.apply(Eq.x_abs_positive_s1, Eq[-3].reversed)

    Eq.xi_is_positive = Eq[-1].this.expr.apply(Algebra.Cond.of.Eq.Cond)

    Eq.xi_all_is_positive = Eq.xi_is_positive.apply(Algebra.All.given.All.limits.delete, index=0)

    Eq << Eq.xi_all_is_positive.this.expr.apply(Bool.All.given.All.AllNot, cond=Equal(i, j))

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << Eq[-1].apply(Algebra.All.given.All.Or.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn_SDiff.given.Or, simplify=None)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Cond.given.Or.domain_defined, wrt=i, simplify=None)

    Eq << Eq.xi_is_positive.apply(Algebra.All.Or.of.All.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(Set.Or.of.NotIn_SDiff, simplify=None)

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq.xi_all_is_positive

    Eq.x_quote_definition = Eq[1].apply(Tensor.EqStackS.of.Eq, (i, 0, k + 1), simplify=False)

    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)

    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])

    Eq << Set.Supset.given.All_In.apply(Eq[-1])

    Eq << Eq[-1].this.expr.simplify()

    Eq << Bool.All_And.given.All.All.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.Any_In.of.In_Cup)

    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-2].reversed.this.expr.apply(Set.EqInter.of.Eq.Eq, Eq[-1])

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(*Eq[-1].lhs.args)

    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq[-2], Eq[-1])

    Eq.set_size_inequality = Eq[-1].this.expr.apply(Algebra.Lt.of.Eq.Lt.subst, Less(Eq[-1].expr.rhs, Eq[-1].expr.rhs + 1, plausible=True))

    Eq << Eq.x_quote_union.this.expr.lhs.apply(Set.Cup.eq.UnionCupS, cond={i, j})

    Eq << Set.CardUnion.le.AddCardS.apply(*Eq[-1].lhs.args)

    Eq << Set.CardCup.le.Sum_Card.apply(*Eq[-2].lhs.args[0].args)

    Eq << Algebra.Le.of.Le.Le.subst.apply(Eq[-2], Eq[-1])

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.set_size_inequality)

    Eq << Eq[-1].this.expr.apply(Algebra.LtAdd.of.Lt.Le)


if __name__ == '__main__':
    run()

# created on 2020-10-03
