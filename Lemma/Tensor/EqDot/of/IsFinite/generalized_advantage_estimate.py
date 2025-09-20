from util import *


@apply
def apply(lt_r, γ, λ, k=None, i=None):
    (δ, t), [S[t]] = lt_r.of(Sup[Abs[Indexed]] < Infinity)

    return Equal((1 - λ) * Sum[k:oo](λ ** k * Sum[i: k + 1](γ ** i * δ[t + i])),
                 (γ * λ) ** Stack[i](i) @ δ[t:])


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Set, Discrete, Tensor

    t, k, i = Symbol(integer=True) # time step counter
    δ = Symbol(shape=(oo,), real=True) # TD residual
    λ, γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Less(Sup[t](Abs(δ[t])), oo), γ, λ, k, i)

    n = Symbol(integer=True)
    Eq << Eq[1].lhs._subs(oo, n).this.find(Sum[~Mul[Sum]]).apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.find(Mul[~Sum]).apply(Algebra.Sum.limits.subst.offset, i)

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Unequal(λ, 1, plausible=True)

    Eq << Algebra.EqSum.of.Ne.geometric_series.apply(Eq[-1], Eq[-2].rhs.find(Mul[~Sum]))

    Eq << Eq[-3].subs(Eq[-1]) * (1 - λ)

    Eq << Eq[-1].this.find(Pow * Pow).apply(Algebra.Mul_Add.eq.AddMulS, 3)

    Eq << Eq[-1].this.rhs.find(Pow * Pow * Pow).args[1:3].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Pow * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Mul.base)

    Eq << Calculus.EqLimit.of.Eq.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Mul)

    Eq << Eq[-1].this.lhs.find(Limit).apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Add)

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Mul)

    Eq.limit = Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Sum)

    i = Eq.limit.rhs.find(Sum).variable
    Eq.lt = Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq.lt.this.lhs.doit()

    Eq << Eq[0].this.lhs.limits_subs(t, i).this.lhs.apply(Algebra.Sup.limits.subst.offset, t)

    Eq << Set.IsReal.Sum.of.LtAbs.IsFinite.apply(Eq.lt, Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(Calculus.Sum.eq.Limit, n)

    Eq.lt = Less(Abs(λ, evaluate=False), 1, plausible=True)

    Eq << Eq.lt.this.lhs.doit()

    Eq << Calculus.Eq_0.Limit.of.LtAbs.geometric_series.apply(Eq.lt, n)

    Eq << Calculus.Eq_0.Limit.of.Eq_0.IsLimited.algebraic_limit_theorem.apply(Eq[-1], Eq[-2])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.T

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Pow)



    # https://arxiv.org/pdf/1506.02438.pdf Eq(16)




if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-10-08
