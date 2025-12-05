from util import *


@apply
def apply(limited_f, limited_g):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, nonzero=True)
    gx, S[(x, x0)] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from Lemma import Calculus, Set, Algebra, Bool

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals - {0}), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq.Limit_A_definition = Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = -Eq.Limit_A_definition.expr.expr.lhs.arg.args[0]
    Eq << Eq[0].subs(A.this.definition.reversed)

    Eq.abs_gt_zero = Set.Gt_0.Abs.of.IsNotZero.apply(Eq[-1])

    Eq.abs_is_positive = Set.IsPositive.Abs.of.IsNotZero.apply(Eq[-1], simplify=None)

    Eq << Set.IsNotZero.Div.of.IsNotZero.apply(Eq[-1])

    Eq << Set.IsPositive.Abs.of.IsNotZero.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Abs.eq.Inv, simplify=None)

    Eq.is_positive_real = Set.In.Mul.Icc.of.In.apply(Eq[-1], ε / 2, simplify=None)

    ε_1 = Symbol(real=True, positive=True)
    δ_1 = Symbol(real=True, positive=True)
    Eq.Limit_B_definition = Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[1], ε_1, δ_1, var='B')

    B = -Eq.Limit_B_definition.expr.expr.lhs.arg.args[0]
    Eq << Algebra.AbsSubMulS.le.AddMulS_AbsSub.apply(f(x), g(x), A, B)

    δ_2 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.Le.of.IsLimited.boundedness.apply(Eq[1], delta=δ_2, var='B')

    B = Eq[-1].expr.expr.rhs
    Eq.le = Eq[-1].this.expr.expr.apply(Algebra.Le.of.Le.Lt.subst, Eq[-2])

    assert B > 0
    Eq << Eq.Limit_A_definition.subs(ε_0, ε / B / 2)

    Eq.lt_fx = Eq[-1].this.expr.expr * B

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq.abs_gt_zero, ε / 2, simplify=None)

    Eq << Eq.Limit_B_definition.subs(ε_1, Eq[-1].lhs)

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq.is_positive_real, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Set.LtMul.of.Lt.IsPositive, Eq.abs_is_positive)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq[-1], Eq.lt_fx)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.LtAdd.of.Lt.Lt)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq.le, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.of.Lt.Le)

    Eq << Eq[-1].this.expr.apply(Bool.Imp.of.AllSetOf)

    Eq << Eq[-1].this.find(Element).apply(Set.In.given.In.Sub, x0)

    Eq << Eq[-1].this.find(Add[Min]).apply(Algebra.Add.eq.Min)

    delta = Symbol(real=True, positive=True)
    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], Min(δ_0, δ_1, δ_2), delta)

    Eq << Eq[-1].this.find(Element).apply(Set.In.given.Add.In.IccAddS, x0)

    Eq << Eq[-1].this.expr.apply(Bool.All.of.Imp)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition





if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-16
# updated on 2021-10-02
