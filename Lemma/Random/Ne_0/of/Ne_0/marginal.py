from util import *


@apply
def apply(given):
    x, given = given.of(Unequal[Pr[Conditioned], 0])
    return Unequal(Pr(x), 0)


@prove
def prove(Eq):
    from Lemma import Random

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(x | y), 0))

    Eq << Random.Ne0ProbJoint.of.Ne0ProbCond.apply(Eq[0])

    Eq << Random.All_NeProb_0.All_NeProb_0.of.All_Ne0ProbJoint.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-22
