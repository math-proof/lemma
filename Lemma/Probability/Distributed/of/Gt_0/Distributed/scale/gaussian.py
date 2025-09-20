from util import *


@apply
def apply(gt_zero, dist, b=0):
    a = gt_zero.of(Expr > 0)
    x, (mu, sigma) = dist.of(Distributed[Symbol, NormalDistribution])
    return Distributed(a * x + b, NormalDistribution(a * mu + b, a ** 2 * sigma))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Probability, Logic

    x = Symbol(real=True, random=True)
    mu, b = Symbol(real=True)
    sigma = Symbol(positive=True)
    a = Symbol(real=True)
    Eq << apply(a > 0, Distributed(x, NormalDistribution(mu, sigma ** 2)), b)

    y = Symbol(real=True)
    Eq << Probability.Distributed.given.Eq.Pr.apply(Eq[-1], y)

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.eq_prob, *Eq[-2:] = Logic.And_And.given.And.Cond.apply(Eq[-1], None)

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Algebra.NeAbs_0.of.Ne_0.apply(Eq[-2])

    Eq << Eq.eq_prob.lhs.this.apply(Probability.Pr.eq.Grad)

    Eq << Probability.EqPr.of.Distributed.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Mul)

    Eq << Algebra.Iff.of.Gt_0.apply(Eq[0], cond=Eq[-1].find(LessEqual))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.doit.Bool)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Integral.eq.Mul.Grad)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp[~Mul]).find(Add).apply(Algebra.Add.eq.Mul.together)





if __name__ == '__main__':
    run()
# created on 2023-04-10
# updated on 2025-04-20
