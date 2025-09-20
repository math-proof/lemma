from util import *


@apply
def apply(self):
    from Lemma.Probability.Expect.ge.Inf import extract
    return LessEqual(self, Sup(*extract(self)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Algebra.All_Le_Sup.apply(Eq[1].rhs)

    Eq << Probability.Pr.ge.Zero.apply(Eq[-2].find(Pr))

    Eq << Algebra.LeMul.of.Ge_0.Le.apply(Eq[-1], Eq[-2])

    Eq << Calculus.LeIntegral.of.Le.apply(Eq[-1], [x.var])

    Eq << Eq[-1].this.find(Integral[Pr]).apply(Probability.Integral.eq.One)





if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-22
