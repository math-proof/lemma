from util import *


@apply
def apply(n, k, s0=None, B=None):
    if s0 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s0 = Symbol(Cup[x[:k]:Stirling.conditionset(n, k, x)](x[:k].cup_finiteset().set))
    if B is None:
        e = Symbol(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol(Cup[e:s0]({e | {n.set}}))

        assert B.definition.variable.is_extended_real
    return Equal(Card(s0), Card(B))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n, k = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    s0_quote = Symbol('s_0_quote', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s0_quote.this.definition

    Eq.s0_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    e = Symbol(etype=dtype.integer.set)
    Eq << Set.All_And.baseset.apply(s0_quote)

    Eq.x_union_s0, *_ = Bool.All.All.of.All_And.apply(Eq[-1], slice(1, None, 2))

    i = Symbol(integer=True)
    x = Eq[0].rhs.variable.base
    j = Symbol(domain=Range(k + 1))
    B = Eq[1].lhs
    Eq.plausible_notcontains = All(NotElement({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(Eq.s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.Any_In.of.In_Cup)

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.EqUnionS.of.Eq.Eq)

    Eq << Eq[-1].this().expr.lhs.simplify()

    Eq << Algebra.Any.of.All_Eq.Any.subst.apply(Eq.x_union_s0, Eq[-1])

    Eq << Eq.plausible_notcontains.this.expr.apply(Set.Eq_Empty.Inter.of.NotIn)

    Eq.all_s0_equality = Eq[-1].this.expr.apply(Set.EqSDiff.of.Inter.eq.Empty)

    x_hat = Symbol(r"\hat{x}", Stack[i](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))
    Eq.x_hat_definition = x_hat[i].this.definition

    Eq << Bool.OrAndS.of.BFn_Ite.apply(Eq.x_hat_definition)

    Eq.B_assertion = Set.All_Any_Eq.split.Imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(Set.EqSDiffS.of.Eq, {n.set})

    Eq << Algebra.All.And.of.Cond.All.apply(Eq.all_s0_equality, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.Any_And.of.Any.All.All_Imp)

    Eq.all_B_contains = Eq[-1].this.expr.expr.apply(Bool.UFn.of.UFn.Eq, swap=True).limits_subs(Eq[-1].variable, Eq.all_s0_equality.variable)

    Eq.all_s0_contains = Set.All_In.split.Imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(Set.EqInter.of.Eq, {n.set})

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(Eq.B_assertion.variable, Eq.B_assertion.expr.variable)

    Eq.all_B_equality = Eq[-1].this.expr.apply(Set.EqUnionS.of.Eq, Eq[-1].variable)

    Eq << Set.Eq.of.All_In.All_In.All_Eq.All_Eq.apply(Eq.all_s0_contains, Eq.all_B_contains, Eq.all_s0_equality, Eq.all_B_equality)





if __name__ == '__main__':
    run()

# created on 2020-08-14
# updated on 2023-05-20
