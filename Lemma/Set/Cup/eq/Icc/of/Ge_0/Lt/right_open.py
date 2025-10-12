from util import *


@apply
def apply(is_nonnegative, lt, k=None):
    a = is_nonnegative.of(Expr >= 0)
    S[a], b = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, right_open=True)), Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Nat

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a >= 0, a < b, k)

    Eq << Nat.EqMin.of.Lt.apply(Eq[1])

    Eq << Algebra.GeAdd.of.Eq.Ge.apply(Eq[-1], Eq[0])

    Eq << Set.Cup.eq.Icc.of.Ge_0.right_open.apply(Eq[-1], k)

    Eq << Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Set.Cup.eq.UnionCupS.apply(Cup[k:b](Eq[-1].lhs.expr), cond=Range(a))

    Eq << Eq[-1].subs(Eq[-2])

    Eq.b_is_nonnegative = Algebra.Ge.of.Ge.Lt.relax.apply(Eq[0], Eq[1])

    Eq << Set.Cup.eq.Icc.of.Ge_0.right_open.apply(Eq.b_is_nonnegative, k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_a = Eq[-1].rhs.args[0]
    Eq << Set.EqSDiffS.of.Eq.apply(Eq[-1], interval_a)

    Eq << Algebra.EqMax.of.Ge.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1]).reversed

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << Set.Any_In.of.Inter.ne.Empty.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(Set.Any_In.of.In_Cup)

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Ge.Le_Sub_1.of.In_Ico)

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.And, slice(0, 3, 2))

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Gt.of.Ge.relax, step=1, ret=0)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.EqMin.of.Gt)

    Eq << Eq[-1].this.expr.args[:2].apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Ge.of.Ge.Ge, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(Algebra.EqMax.of.Ge)

    Eq << Eq[-1].this.expr.args[:2].apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.expr.args[0].apply(Set.Lt.of.Ioc.ne.Empty)

    Eq << Set.Eq.of.Inter.eq.Empty.Eq_SDiff.apply(Eq.is_empty, Eq.eq_complement)





if __name__ == '__main__':
    run()
# created on 2021-02-20
# updated on 2023-11-05
