from util import *


@apply
def apply(self):
    from Lemma.Probability.Expect.ge.Inf import extract
    return LessEqual(Inf(*extract(self)), self, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Probability.Expect.ge.Inf.apply(Eq[0].find(Expectation))

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-22
