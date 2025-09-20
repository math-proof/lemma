from util import *


@apply
def apply(self, *, simplify=True):
    (expr, *limits_l), *limits_e = self.of(Expectation[Limit])
    return Equal(self, Limit(Expectation(expr, *limits_e), *limits_l), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True)
    Eq << apply(Expectation(Limit[n:oo](f[n](x))))

    Eq << Eq[0].this.rhs.apply(Probability.Limit.eq.Expect)


if __name__ == '__main__':
    run()
# created on 2023-04-04
