from util import *


def is_differentiable_at(cond, dir=1):
    (dfx, domain), (x, a, b) = cond.of(All[Element])
    fx, (S[x + dir * S.Infinitesimal], S[1]) = dfx.of(Derivative)
    assert domain in Interval(-oo, oo, left_open=False, right_open=False)
    return fx, (x, a, b)

@apply
def apply(lt, is_continuous, left_is_real, right_is_real, equal):
    a, b = lt.of(Less)
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_continuous
    fx, (x, S[a], S[b]) = of_continuous(is_continuous)
    S[fx], S[(x, a, b)] = is_differentiable_at(left_is_real)
    S[fx], S[(x, a, b)] = is_differentiable_at(right_is_real, -1)

    S[fx._subs(x, a)], S[fx._subs(x, b)] = equal.of(Equal)

    return Any[x:a:b](Derivative[x - S.Infinitesimal](fx) * Derivative[x + S.Infinitesimal](fx) <= 0)


@prove
def prove(Eq):
    from Lemma import Calculus, Set, Algebra, Bool

    a, b, x = Symbol(real=True)
    f = Function(shape=(), real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(
        a < b,
        is_continuous(f, a, b),
        All[x:a:b](Element(Derivative[x + S.Infinitesimal](f(x)), ExtendedReals)),
        All[x:a:b](Element(Derivative[x - S.Infinitesimal](f(x)), ExtendedReals)),
        Equal(f(a), f(b)))

    Eq << Eq[2].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Eq[3].this.find(Derivative).apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Set.Subset.Finset.of.Lt.apply(Eq[0], simplify=None)

    Eq.eq_intersect = Set.EqInter.of.Subset.apply(Eq[-1])

    ξ = Eq[1].variable
    c0, c1 = Symbol(real=True)
    Eq << Calculus.Any.All.Ge.of.Lt.IsContinuous.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c0)

    # Eq << Eq[-1].this.expr.expr.reversed
    Eq << Algebra.Or.Any.of.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Calculus.Any.All.Le.of.Lt.IsContinuous.extreme_value_theorem.apply(*Eq[:2]).limits_subs(ξ, c1)

    Eq << Algebra.Or.Any.of.Any.split.apply(Eq[-1], cond={a, b})

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.find(And[Or]).apply(Bool.OrAndS.of.And_Or, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.Any.And.of.Any.Any)

    Eq << Eq[-1].this.find(And).apply(Bool.Cond.of.And, 1)

    Eq << Eq[-1].this.find(And).apply(Bool.Cond.of.And)

    Eq << Bool.Cond.given.And.Imp.apply(Eq[5], cond=Eq[-1])

    Eq.any_max, Eq.any_min, Eq.any_boundary = Bool.ImpOr.given.Imp.Imp.apply(Eq[-1], None)

    Eq <<= Eq.any_min.this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf, simplify=None), \
        Eq.any_max.this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf, simplify=None)

    Eq <<= Eq[1] & Eq[2] & Eq[3]

    Eq <<= Bool.Imp.given.And.Imp.invert.apply(Eq[-3], cond=Eq[-1]), Bool.Imp.given.And.Imp.invert.apply(Eq[-2], cond=Eq[-1])

    Eq <<= Bool.Or.given.Cond.apply(Eq[-3], 0), Bool.Or.given.Cond.apply(Eq[-1], 0)

    Eq <<= Eq[-4].this.lhs.args[:2].apply(Bool.Any_And.of.Any.All, simplify=None), \
        Eq[-2].this.lhs.args[:2].apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq <<= Eq[-2].this.lhs.args[:2].apply(Bool.Any_And.of.Any.All, simplify=None), \
        Eq[-1].this.lhs.args[:2].apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq.Any_And_min = Eq[-2].this.lhs.apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq.Any_And_max = Eq[-1].this.lhs.apply(Bool.Any_And.of.Any.All, simplify=None)

    et = And(*Eq.Any_And_max.lhs.expr.args)
    Eq <<= et.this.apply(Bool.Cond.of.And, slice(0, 4)), et.this.apply(Bool.Cond.of.And, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[LessEqual]).apply(Set.AllIn_SDiff.of.All, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[LessEqual]).apply(Set.AllIn_SDiff.of.All, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Le_0.Subs.Grad.of.In_Icc.IsContinuous.IsExtendedReal.All_Le), Eq[-1].this.rhs.apply(Calculus.Ge_0.Subs.Grad.of.In_Icc.IsContinuous.IsExtendedReal.All_Le)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.le.Zero.of.Le_0.Ge_0)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1], 0)

    Eq << Bool.Imp.Any.of.Imp.apply(Eq[-1], c1)

    Eq << Eq[-1].this.rhs.apply(Bool.AnySetOf.of.Any_And, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c1, x)

    et = And(*Eq.Any_And_min.lhs.expr.args)
    Eq <<= et.this.apply(Bool.Cond.of.And, slice(0, 4)), et.this.apply(Bool.Cond.of.And, slice(3, 2, -1))

    Eq <<= Eq[-2].this.rhs.find(All[GreaterEqual]).apply(Set.AllIn_SDiff.of.All, Interval.open(a, b), simplify=None), Eq[-1].this.rhs.find(All[GreaterEqual]).apply(Set.AllIn_SDiff.of.All, Interval.open(a, b), simplify=None)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Ge_0.Subs.Grad.of.In_Icc.IsContinuous.IsExtendedReal.All_Ge), Eq[-1].this.rhs.apply(Calculus.Le_0.Subs.Grad.of.In_Icc.IsContinuous.IsExtendedReal.All_Ge)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.le.Zero.of.Le_0.Ge_0)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1], 0)

    Eq << Bool.Imp.Any.of.Imp.apply(Eq[-1], c0)

    Eq << Eq[-1].this.rhs.apply(Bool.AnySetOf.of.Any_And, 1)

    Eq << Eq[-1].this.rhs.limits_subs(c0, x)

    Eq << Eq.any_boundary.this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf, simplify=None)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[4], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.find(And).args[:-1].apply(Set.Eq.of.In_Finset.In_Finset.Eq)

    Eq << Eq[-1].this.find(And).apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.of.Le.Ge)

    Eq << Eq[-1].this.find(Equal).apply(Calculus.EqGrad.of.Eq, (x,))

    Eq << Eq[-1].this.find(Equal).rhs.doit()

    Eq << Eq[-1].this.find(Equal).apply(Calculus.And.Eq_Grad.of.Eq_Grad)

    Eq << Eq[-1].this.find(And).apply(Algebra.EqMul.of.Eq.Eq)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Le.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_SDiff.of.All, Interval.open(a, b))

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subst, x, (a + b) / 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.of.All.subst, x, (a + b) / 2)

    Eq << Bool.Imp.given.Cond.apply(Eq[-1])

    Eq << Set.In.Icc.of.Lt.average.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-10-14
# updated on 2023-11-10
0
