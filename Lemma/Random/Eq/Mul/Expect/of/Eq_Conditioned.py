from util import *


@apply
def apply(self):
    (y, x), S[y] = self.of(Equal[Conditioned])
    x, S[x.var] = x.of(Equal)
    assert y.is_random and x.is_random
    return Equal(Expectation(x * y), Expectation(x) * Expectation(y))


@prove
def prove(Eq):
    from Lemma import Random, Real

    y, x = Symbol(real=True, random=True) # rewards
    Eq << apply(Equal(y | x, y))

    Eq << Eq[-1].this.lhs.apply(Random.Expect.eq.Integral)

    Eq << Random.Eq.Mul.Prob.of.Eq_Conditioned.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Real.Integral.limits.separate)

    Eq << Eq[-1].this.lhs.apply(Real.Integral.eq.Mul)

    Eq << Eq[-1].this.find(Integral).apply(Random.Integral.eq.Expect)

    Eq << Eq[-1].this.find(Integral).apply(Random.Integral.eq.Expect)

    # https://danieltakeshi.github.io/2017/03/28/going-deeper-into-reinforcement-learning-fundamentals-of-policy-gradients/ (Approximation (ii))


if __name__ == '__main__':
    run()
# created on 2023-04-09
