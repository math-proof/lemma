from util import *


@apply
def apply(self, *, simplify=True):
    (expr, *limits_e), *limits_l = self.of(Limit[Expectation])
    for n, *cond in limits_l:
        assert not any(limit._has(n) for limit in limits_e)

    return Equal(self, Expectation(Limit(expr, *limits_l), *limits_e), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability, Calculus

    n = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True)
    Eq << apply(Limit[n:oo](Expectation(f[n](x))))

    Eq << Eq[0].this.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Integral)

    Eq << Eq[-1].this.lhs.find(Limit).apply(Calculus.Limit.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2023-04-04
