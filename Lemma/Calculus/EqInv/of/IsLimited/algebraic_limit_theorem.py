from util import *


@apply
def apply(is_limited):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, nonzero=True)

    return Equal(Limit[x:x0](1 / fx), 1 / is_limited.lhs)


@prove
def prove(Eq):
    from Lemma import Calculus, Set, Algebra, Bool

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals - {0}))

    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = Eq[-1].find(Abs[Add[-~Symbol]])
    Eq.is_limited = A.this.definition.reversed

    Eq.is_nonzero_real = Eq[0].subs(Eq.is_limited)

    Eq << Set.Ne_0.of.In.apply(Eq.is_nonzero_real)

    Eq << Algebra.EqInv.of.Ne_0.Eq.apply(Eq[-1], Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.is_limited)

    δ_1 = Symbol(positive=True)
    Eq << Calculus.Any.All.Lt.of.Eq_Limit.In.half.apply(Eq.is_limited, Eq.is_nonzero_real, delta=δ_1)

    Eq.A_is_positive = Set.Gt_0.Abs.of.IsNotZero.apply(Eq.is_nonzero_real)

    Eq << Algebra.Any.All.And.of.Cond.Any_All.apply(Eq.A_is_positive / 2, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.LtInv.of.Gt_0.Gt)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq.A_is_positive)

    Eq << Algebra.Any.All.And.of.Cond.Any_All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.LtMul.of.Gt_0.Lt)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.LtMul.of.Lt.Lt)

    Eq << Eq[-1].this.find(Mul[Abs]).apply(Algebra.MulAbsS.eq.AbsMul)

    Eq << Eq[-1].this.find(Abs[~Mul]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.expr.expr.lhs.apply(Algebra.Abs.Neg)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Set.Lt.given.In.Icc)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Set.Lt.given.In.Icc)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    ε, δ = Symbol(positive=True)
    Eq << Algebra.Or.of.Cond.subst.apply(Eq[-1], ε_0, abs(A) ** 2 / 2 * ε)

    Eq << Algebra.Gt_0.Square.of.Gt_0.apply(Eq.A_is_positive) * ε / 2

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-18
# updated on 2023-04-16
