from util import *


@apply
def apply(self):
    from Lemma.Random.Sum.eq.One.Conditioned import extract
    return Equal(self, extract(Integral, self))


@prove
def prove(Eq):
    from Lemma import Random

    x, y = Symbol(real=True, random=True)
    Eq << apply(Integral[x.bvar](Pr(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(Random.All_Eq_DivProbS)

    Eq << Eq[-1].this.find(Integral).apply(Random.All_EqIntegral_ProbJoint.of.PSpace_Joint)





if __name__ == '__main__':
    run()
# created on 2021-07-20
# updated on 2023-03-25
