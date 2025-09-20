from util import *


@apply
def apply(self):
    (X, (S[X], n)), (S[X], die) = self.of(Expectation[Conditioned[Symbol, Symbol > Symbol / 2]])
    S[n] = die.of(DieDistribution)
    return Equal(self, (n + 1) / 2 + floor(n / 2) / 2)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    X = Symbol(integer=True, random=True)
    Eq << apply(Expectation[X:DieDistribution(n)](X | (X > n / 2)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.lhs.ratsimp()

    


if __name__ == '__main__':
    run()
# created on 2021-08-06
# updated on 2023-03-29
