from util import *


@apply
def apply(eq, eq1):
    from Lemma.Discrete.Gt_0.of.Eq.Eq.catalan import is_catalan_series
    Cn, n = is_catalan_series(eq, eq1)
    return Equal(Cn, binomial(n * 2, n) / (n + 1))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Discrete, Set, Bool, Finset

    n, k = Symbol(integer=True)
    # n = Symbol(integer=True, nonnegative=True)
    C = Symbol(shape=(oo,), integer=True)
    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    @Function(extended_real=True)
    def g(x):
        return Sum[n:oo](C[n] * x ** n)
    x = Symbol(domain=Interval(0, S.One / 4, left_open=True))
    Eq.g_definition = g(x).this.defun()

    Eq << Eq[1] * x ** n

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (n, 0, oo))

    Eq << Calculus.Mul.Sum.eq.Sum.Sum.apply(C, C, n=n, k=k, x=x)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition ** 2

    Eq.g_squared = Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition.this.rhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subst.offset, 1)

    Eq << Eq.g_squared * x

    Eq << Eq[-1].this.lhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-3])

    Eq << Algebra.Eq_0.of.Eq.apply(Eq[-1])

    Eq.ou = Eq[-1].apply(Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic, x=g(x), simplify=False)

    Eq.negative_sqrt = Eq.ou.args[0].copy(plausible=True)

    Eq.positive_sqrt = Any[x:x < S.One / 4](Eq.ou.args[1], plausible=True)

    x_quote = Symbol(domain=Interval(0, S.One / 4, left_open=True, right_open=True))
    x_var = Eq.positive_sqrt.variable
    Eq.positive_sqrt_quote = Eq.positive_sqrt.limits_subs(x_var, x_quote)

    Eq << Derivative[x_quote](Eq.positive_sqrt_quote.rhs).this.doit()

    Eq << Less(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].this.lhs.subs(Eq[-2].reversed)

    Eq << Calculus.Gt.of.Lt_0.monotony.apply(Eq[-1])

    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq.positive_sqrt_quote, Eq[-1], reverse=True)

    Eq.any_gt = Algebra.Any.of.Any.limits.relax.subst.apply(Eq[-1], x_quote, x)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq.g_definition, (x,), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum.eq.AddSumS, cond={0})

    Eq.g_derivative = Eq[-1].this.rhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Discrete.Gt_0.of.Eq.Eq.catalan.apply(Eq[0], Eq[1])

    Eq << Eq[-1] * x ** (n - 1)

    Eq << Algebra.Gt.Sum.Mul.of.Gt.apply(Eq[-1], (n, 0, oo))

    Eq << Eq[-1].this.lhs.subs(Eq.g_derivative.reversed)

    Eq << Calculus.Le.of.Gt_0.monotony.apply(Eq[-1])

    Eq << Eq.ou.subs(x, S.One / 4)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.any_gt)

    Eq << ~Eq.positive_sqrt

    Eq << Bool.Or_Not.of.All.apply(Eq[-1])

    Eq << Eq[-1].subs(x_var, x)

    Eq << Eq[-1].this.find(NotElement).apply(Set.Or.of.NotIn_Icc)

    Eq << Eq[-1].this.args[1].apply(Algebra.Eq.of.Ge.squeeze)

    Eq.all_ne = Bool.All.of.All_OrNot.apply(Eq[-1], wrt=x)

    Eq << Eq.ou.apply(Bool.AndAllSSetOf.of.All, cond=x < S.One / 4)

    Eq << Bool.Cond.of.And.apply(Eq[-1], index=1)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], Eq[-1].variable, x)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], wrt=x)

    Eq <<= Eq.all_ne & Eq[-1]

    Eq << Bool.All.of.All_And.apply(Eq[-1], index=0)

    Eq << Bool.Or_Not.of.All.apply(Eq[-1])

    Eq << Bool.All.of.Cond.apply(Eq[-1], x)

    Eq << Bool.Or_Not.of.All.apply(Eq[-1])

    Eq << Eq.negative_sqrt.apply(Bool.All.given.All.AllNot, cond=x < S.One / 4)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Bool.All.given.All_Or_Not.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(Set.NotIn.given.Or.Icc)

    Eq << Calculus.Pow.eq.Sum.Binom.apply((1 - 4 * x) ** (S.One / 2), n=n)

    Eq << Eq[-1].this.rhs().find(Binomial).apply(Discrete.Binom.eq.Mul.half)

    Eq << Eq[-1].this.rhs.args[1].expr.powsimp()

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.eq.Add.shift)

    Eq << 1 - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.subst.offset, 1)

    Eq << Eq[-1] / (x * 2)

    Eq << Eq[-1] + Eq.negative_sqrt

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.distribute)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Div.cancel, 2)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom.decrease)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.rhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.rhs.expr.ratsimp()

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq.g_definition)

    Eq << Calculus.Eq.series.Infty.of.Eq.coefficient.apply(Eq[-1].reversed, x=x)


if __name__ == '__main__':
    run()

# created on 2020-10-21
# updated on 2023-06-03
