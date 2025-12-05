from util import *


@apply
def apply(lt, all_gt, limit_is_real_fx, limit_is_real_gx):
    a, b = lt.of(Less)
    (lhs, rhs), (x, domain) = all_gt.of(All[Greater])
    S[a], S[b] = domain.of(Interval)

    (S[lhs], (x, x0)), R = limit_is_real_fx.of(Element[Limit])
    assert R in Reals
    (S[rhs], limit), R = limit_is_real_gx.of(Element[Limit])
    assert R in Reals
    assert limit == (x, x0)

    x0, dir = x0.clear_infinitesimal()
    assert lhs.is_continuous_at(x, domain)
    assert rhs.is_continuous_at(x, domain)
    if dir < 0:
        x0 = b
        assert domain.right_open
    elif dir > 0:
        x0 = a
        assert domain.left_open

    return GreaterEqual(Limit[x:x0 + dir](lhs), Limit[x:x0 + dir](rhs))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Bool

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    domain = Interval(a, b, right_open=True)
    f, g = Function(real=True, continuous=domain)
    Eq << apply(a < b, All[x:domain](Greater(f(x), g(x))), Element(Limit[x:b - S.Infinitesimal](f(x)), Reals), Element(Limit[x:b - S.Infinitesimal](g(x)), Reals))

    Eq <<= Calculus.All_EqLimit.IsContinuous.Icc.apply(f(x), (x, domain)), Calculus.All_EqLimit.IsContinuous.Icc.apply(g(x), (x, domain))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.expr.apply(Calculus.Eq_Limit.Sub.of.Eq_Limit.Eq_Limit)

    xi = Eq[-1].variable
    Eq <<= Eq[1].this.expr.apply(Algebra.Gt_0.of.Gt)

    Eq <<= Eq[-1].limits_subs(x, xi)

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq[-1].this.expr.apply(Algebra.Gt.of.Eq.Gt.subst)

    Eq <<= Bool.Imp.of.AllSetOf.apply(Eq[-1])

    epsilon = Symbol(positive=True)
    Eq <<= Eq[-1].subs(xi, b - epsilon)

    Eq <<= Eq[-1].this.lhs.apply(Set.In_Icc.given.InNeg)

    Eq <<= Eq[-1].this.lhs.apply(Set.In.given.Add.In.IccAddS, b)

    Eq <<= Eq[-1].this.lhs.apply(Set.In_Ico.given.Ge.Lt)

    Eq << Bool.All.of.Imp.apply(Eq[-1])

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Calculus.Limit.ge.Zero.of.Gt_0.All_GtLimit__0.apply(Eq[-1], Eq[-2])

    Eq << Calculus.EqSub.of.IsLimited.IsLimited.algebraic_limit_theorem.apply(Eq[2], Eq[3])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Set.GeAdd.of.Ge.In.apply(Eq[-1], Eq[3])


if __name__ == '__main__':
    run()
# created on 2020-06-26
