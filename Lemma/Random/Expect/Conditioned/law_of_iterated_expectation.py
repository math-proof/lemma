from util import *


@apply
def apply(self, *vars):
    from Lemma.Random.Expect.law_of_iterated_expectation import rewrite
    return Equal(self, rewrite(self, *vars))


@prove
def prove(Eq):
    from Lemma import Random

    x, y, z = Symbol(real=True, random=True)
    f = Function(real=True, shape=())
    Eq << apply(Expectation(f(x, y, z) | z), y)

    Eq << Eq[-1].this.rhs.apply(Random.Expect.Conditioned.law_of_total_expectation)




if __name__ == '__main__':
    run()
# created on 2023-04-22
