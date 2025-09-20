from util import *


@apply
def apply(n, k, s2=None, B=None):
    from sympy.functions.combinatorial.numbers import Stirling
    if s2 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
        s2 = Symbol(Cup[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].cup_finiteset().set))
    e = Symbol(**s2.etype.dict)

    if B is None:
        x = s2.definition.variable.base
        s0 = Symbol(Cup[x[:k]:Stirling.conditionset(n, k, x)](x[:k].cup_finiteset().set))

        B = Symbol(Cup[e:s0]({e | {n.set}}))

    return Equal(conditionset(e, Element({n}, e), s2), B)


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    k, n = Symbol(integer=True, positive=True)
    Eq << apply(n, k)

    s2 = Eq[0].lhs
    s2_quote = Symbol('s_quote_2', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition

    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    s0 = Eq[1].lhs
    s0_quote = Symbol('s_quote_0', conditionset(Eq[1].rhs.variable, Eq[1].rhs.limits[0][1]))
    Eq << s0_quote.this.definition

    Eq << imageset(Eq[1].rhs.variable, Eq[1].rhs.expr.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[1].reversed).reversed

    s0_definition = Eq[-1]
    e = Symbol(etype=dtype.integer.set)
    s0_ = imageset(e, Union(e, {n.set}), s0)
    plausible0 = Subset(s0_, s2, plausible=True)
    Eq << plausible0

    Eq << Set.Subset.given.All_In.apply(Eq[-1])

    Eq << Eq[-1].this.limits[0][1].subs(s0_definition)

    Eq << Eq[-1].subs(Eq.s2_definition)

    s0_plausible = Eq[-1]
    Eq.s2_quote_definition = Set.All_CupFinset.eq.Range.apply(s2_quote)

    Eq << Set.All_CupFinset.eq.Range.apply(s0_quote)

    Eq.x_abs_positive = Logic.All.of.All_And.apply(Eq[-1])
    Eq.x_abs_sum = Logic.All.of.All_And.apply(Eq[-1], 1)
    Eq.x_union_s0 = Logic.All.of.All_And.apply(Eq[-1], 2)

    i = Eq.x_union_s0.lhs.limits[0][0]
    x = Eq.x_union_s0.variable.base
    Eq.x_k_definition = Any[x[k]](Equal(x[k], {n}), plausible=True)
    return
    Eq << Eq.x_k_definition.simplify()

    Eq << Eq.x_union_s0.this.expr.apply(Set.eq.then.eq.union, x[k])

    return
    Eq << Eq[-1].subs(Eq.x_k_definition)
    x_union = Eq[-1]
    Eq << Eq.x_k_definition.apply(Set.eq.then.eq.set, simplify=False)
    Eq << Eq[-1].apply(Set.eq.then.eq.union, x[:k].cup_finiteset())
    Eq << s0_plausible.subs(Eq[-1].reversed)
    Eq << Eq[-1].this.expr.expr.apply(Set.element.of.contains.split.imageset)
    Eq << Eq[-1].this.expr.expr.rhs.definition
    Eq << Eq.x_k_definition.apply(Algebra.eq.then.eq.abs)
    Eq << Eq[-1] + Greater(1, 0, plausible=True)
    Eq << Eq.x_abs_sum + Eq[-2]
    Eq <<= Eq.x_abs_positive & Eq[-2]
    Eq <<= x_union & Eq[-1] & Eq[-2]
    j = Symbol(domain=Range(k + 1))
    Eq << plausible0.subs(Eq[2].reversed)
    Eq << s2.this.bisect(conditionset(e, Element({n}, e), s2))
    Eq.subset_B = Subset(Eq[-1].rhs.args[0], Eq[-2].lhs, plausible=True)  # unproven
    Eq.supset_B = Supset(Eq[-1].rhs.args[0], Eq[-2].lhs, plausible=True)  # unproven
    Eq << Eq.supset_B.subs(Eq[2])
    Eq << Set.supset.of.All_contains.apply(Eq[-1])
    Eq << Eq[-1].this.expr.simplify()
    Eq << Eq.subset_B.subs(Eq[2])
    Eq << Set.Subset.given.All_In.apply(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Set.element.of.any_eq.split.imageset)
    Eq << Algebra.All.of.All_And.conditionset.apply(Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.apply(Algebra.et.of.Any_And, simplify=None)
    Eq.subset_B_definition = Eq[-1].this.expr.expr.apply(Set.et.of.et.contains)
    num_plausibles = len(Eq.plausibles_dict)
    Eq.plausible_notcontains = All(NotElement({n}, e), (e, s0), plausible=True)
    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(s0_definition)
    Eq << ~Eq[-1]
    Eq << Eq[-1].apply(Set.element.then.any_contains.split.cup)
    Eq << Algebra.All.any.then.Any_And.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=False)
    Eq << Eq[-1].this.expr.apply(Set.Eq.Eq.then.eq.Union)
    Eq << Eq[-1].this().expr.lhs.simplify()
    Eq << Eq[-1].subs(Eq.x_union_s0)
    assert num_plausibles == len(Eq.plausibles_dict)
    Eq << Eq.plausible_notcontains.apply(Set.notcontains.then.is_empty.intersection)
    Eq << Eq[-1].apply(Set.is_empty.then.Eq.Complement).limits_subs(Eq[-1].variable, Eq.subset_B_definition.expr.variable)
    Eq << Eq.subset_B_definition.subs(Eq[-1])
    s2_n = Symbol("s_{2, n}", conditionset(*Eq[-1].limits[0]))
    Eq.s2_n_definition = s2_n.this.definition
    Eq << Set.then.all.baseset.apply(s2_n)
    Eq << Eq[-1].subs(Eq.s2_definition)
    Eq << Logic.All.of.All_And.apply(Eq[-1])
    Eq.s2_n_assertion = Eq[-2].this.expr.apply(Set.element.of.any_eq.split.imageset)
    Eq << Eq[-1].subs(Eq.s2_n_assertion)
    Eq << Eq[-1].apply(Set.element.then.any_contains.split.cup)
    Eq.x_j_definition = Eq[-1].limits_subs(Eq[-1].variable, j).reversed
    Eq.x_abs_positive_s2, Eq.x_abs_sum_s2, Eq.x_union_s2 = Logic.All.of.All_And.apply(Eq.s2_quote_definition, simplify=None)
    Eq << Algebra.All.any.then.Any_And.apply(Eq.x_union_s2, Eq.x_j_definition)
    Eq << Eq[-1].this.expr.apply(Set.Eq.Eq.then.Eq.Complement, swap=True)
    Eq << Eq[-1].this.expr.lhs.args[0].bisect({j})
    Eq << Eq[-1].this.expr.lhs.apply(Set.Complement.to.union, evaluate=True)
    Eq << Eq.s2_quote_definition.this.expr.apply(Set.Eq.Eq.All_is_positive.then.eq.Stirling2)
    Eq << Eq[-2].subs(Eq[-1])
    x_tilde = Symbol(r"\tilde{x}", Stack[i:k](Piecewise((x[i], i < j), (x[i + 1], True))))
    Eq.x_tilde_definition = x_tilde[i].this.definition
    Eq << Set.eq.then.eq.cup.apply(Eq.x_tilde_definition, (i, 0, k))
    Eq << Eq[-1].this.rhs.args[1].limits_subs(i, i - 1)
    Eq.x_tilde_union = Eq[-1].subs(Eq[-3])
    Eq.x_tilde_abs = Eq.x_tilde_definition.apply(Algebra.eq.then.eq.abs)
    Eq << Eq.x_tilde_abs.apply(Algebra.eq.then.eq.sum, (i, 0, k))
    Eq << Eq[-1].this.rhs.args[0].limits_subs(i, i - 1)
    Eq << Eq.x_j_definition.apply(Algebra.eq.then.eq.abs)
    Eq.x_tilde_abs_sum = Eq[-2].subs(Eq.x_abs_sum_s2, Eq[-1])
    Eq << Algebra.eq.then.ou.two.apply(Eq.x_tilde_abs)
    Eq << Eq[-1].apply(Algebra.Cond.then.all.restrict, (i, i < j))
    Eq << Eq[-2].apply(Algebra.Cond.then.all.restrict, (i, i >= j))
    Eq << Eq[-2].subs(Eq.x_abs_positive_s2)
    Eq << Eq[-2].subs(Eq.x_abs_positive_s2.limits_subs(i, i + 1))
    Eq <<= Eq[-1] & Eq[-2]
    Eq <<= Eq[-1] & Eq.x_tilde_abs_sum & Eq.x_tilde_union
    Eq << Eq[-1].func(Element(x_tilde, s0_quote), *Eq[-1].limits, plausible=True)
    Eq << Eq[-1].this.expr.rhs.definition
    Eq << Eq[-1].this.expr.args[0].simplify()
    def construct_finite_set(cls, base, start=None, stop=None, x=None):
        if start is None:
            start = S.Zero
        if stop is None:
            stop = base.shape[-1]
        if x is None:
            x = base.generate_var(start.free_symbols | stop.free_symbols, integer=True)
        return cls(base[x].set, (x, start, stop - 1))
    Eq.x_tilde_set_in_s0 = Eq[-3].func(Element(construct_finite_set(Cup, x_tilde), s0), *Eq[-3].limits, plausible=True)
    Eq << Eq.x_tilde_set_in_s0.subs(s0_definition)
    Eq << Eq[-1].this.expr.apply(Set.element.of.any_eq.split.imageset)
    Eq << Set.eq.then.eq.cup_finiteset.apply(Eq.x_tilde_definition, (i, 0, k))
    Eq << Eq[-1].subs(Eq.x_j_definition)
    Eq << Eq[-1].subs(Eq.s2_n_assertion.reversed)
    Eq << Eq.x_tilde_set_in_s0.subs(Eq[-1])
    Eq << Eq[-1].this.limits[0].subs(Eq.s2_n_definition)
    Eq.subset_B_plausible = Eq.subset_B_definition.apply(Set.eq.then.eq.union, {n.set})
    Eq << All(Eq.subset_B_plausible.limits[0][1], *Eq.subset_B_plausible.limits, plausible=True)
    Eq << Eq[-1].simplify()
    Eq << Eq[-1].apply(Set.element.then.eq.Union)
    Eq << Eq.subset_B_plausible.subs(Eq[-1])
    Eq <<= Eq.supset_B & Eq.subset_B


if __name__ == '__main__':
    run()

# created on 2020-09-29
