from util import *


@apply
def apply(self):
    cond = self.of(Pr)
    if cond.is_Conditioned:
        cond, given = cond.args
    else :
        given = None

    return Equal(self, 1 - Pr(cond.invert(), given=given))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus

    x = Symbol(real=True, random=True)
    Eq << apply(Pr(x >= 0))

    Eq << Eq[0].this.lhs.apply(Probability.Pr.eq.Integral)

    Eq << Eq[-1].this.rhs.find(Pr).apply(Probability.Pr.eq.Integral)

    Eq << Algebra.Eq.given.Eq.transport.apply(Eq[-1], rhs=1)

    Eq << Eq[-1].this.lhs.apply(Calculus.Add.eq.Integral.concat)

    Eq << Eq[-1].this.lhs.apply(Probability.Integral.eq.One)


if __name__ == '__main__':
    run()
# created on 2023-04-19
