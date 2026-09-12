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

    Eq << Random.Ne_0.of.Ne_0.joint.apply(Eq[0])

    Eq << Random.NePr_0.NePr_0.of.NePr__0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-22
