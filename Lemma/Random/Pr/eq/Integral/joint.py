from util import *


@apply
def apply(self, y):
    from Lemma.Random.Pr.eq.Sum.joint import rewrite
    return Equal(self, rewrite(Integral, self, y))


@prove
def prove(Eq):
    from Lemma import Random, Bool

    x, y = Symbol(real=True, random=True)
    Eq << apply(Pr(x), y)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(Pr(x), 0))

    Eq << Eq[-1].this.lhs.apply(Random.Pr.eq.Mul.Pr.of.Ne_0.bayes, y)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(Integral).apply(Random.Integral.eq.One.Conditioned)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(Random.Eq_0.of.Eq_0.joint, y)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-21
# updated on 2023-03-30
