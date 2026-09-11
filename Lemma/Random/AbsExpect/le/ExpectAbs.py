from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    return LessEqual(Abs(self), Expectation(Abs(expr), *limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Random, Int

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Random.Expect.le.ExpectAbs.apply(Eq[0].lhs.find(Expectation))

    Eq << Random.Expect.le.ExpectAbs.apply(Eq[0].lhs.find(Expectation)._subs(f(x), -f(x)))

    Eq << -Eq[-1].this.lhs.apply(Random.Expect.eq.Mul)

    Eq << Int.LeAbs.of.LeNeg.Le.apply(Eq[-3], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-15
