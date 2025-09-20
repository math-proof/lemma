from util import *


@apply
def apply(given):
    fx, gx = given.of(Equal)
    return Equal(Expectation(fx), Expectation(gx))


@prove
def prove(Eq):
    from Lemma import Probability

    x = Symbol(real=True, random=True)
    f, g = Function(real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[0].subs(x, x.var)


    Eq << Eq[-2].subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-04-04
