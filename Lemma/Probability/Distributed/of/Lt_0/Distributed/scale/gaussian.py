from util import *


@apply
def apply(lt_zero, dist, b=0):
    a = lt_zero.of(Expr < 0)
    x, (mu, sigma) = dist.of(Distributed[Symbol, NormalDistribution])
    return Distributed(a * x + b, NormalDistribution(a * mu + b, a ** 2 * sigma))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Probability, Bool, Complex, Complex, Complex

    x = Symbol(real=True, random=True)
    mu, b = Symbol(real=True)
    sigma = Symbol(positive=True)
    a = Symbol(real=True)
    Eq << apply(a < 0, Distributed(x, NormalDistribution(mu, sigma ** 2)), b)

    y = Symbol(real=True)
    Eq << Probability.Distributed.given.Eq.Pr.apply(Eq[-1], y)

    Eq << Algebra.EqAbs.of.Lt_0.apply(Eq[0])

    Eq << Eq[-2].this.subs(Eq[-1])

    Eq.eq_prob, *Eq[-2:] = Bool.And_And.given.And.Cond.apply(Eq[-1], None)

    Eq << Algebra.Ne.of.Lt.apply(Eq[0])

    Eq << Complex.NeNorm_0.of.Ne_0.apply(Eq[-2])

    Eq << Eq.eq_prob.lhs.this.apply(Probability.Pr.eq.Grad)

    Eq << Probability.EqPr.of.Distributed.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Mul)

    Eq << Algebra.Iff.of.Lt_0.apply(Eq[0], cond=Eq[-1].find(LessEqual))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.doit.Bool)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Integral.eq.Mul.Grad)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp[~Mul]).find(Add).apply(Algebra.Add.eq.Mul.together)





if __name__ == '__main__':
    run()
# created on 2023-04-11
# updated on 2025-04-20
