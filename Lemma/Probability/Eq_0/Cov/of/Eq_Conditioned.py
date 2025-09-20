from util import *


@apply
def apply(eq_conditioned, swap=False):
    (y, x), S[y] = eq_conditioned.of(Equal[Conditioned])
    x, x_var = x.of(Equal)
    if swap:
        x, y = y, x
    return Equal(Covariance(x, y), Zeros(*x.shape).outer_product(Zeros(*y.shape)))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(y | x, y))

    Eq << Eq[1].this.lhs.apply(Probability.Cov.eq.Sub.Expect)

    Eq << Probability.Eq.Mul.Expect.of.Eq_Conditioned.apply(Eq[0])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-04-19
