from util import *


@apply
def apply(given_equality, ne_zero):
    x, x_var = ne_zero.of(Unequal[Pr[Equal], 0])

    (S[x], y), S[x] = given_equality.of(Equal[Conditioned])
    y, y_var = y.of(Equal)

    return Equal(y | x, y)


@prove
def prove(Eq):
    from Lemma import Probability
    x, y = Symbol(real=True, random=True)

    Eq << apply(Equal(x | y, x), Unequal(Pr(x), 0))

    Eq << Probability.Eq.Mul.Pr.of.Eq_Conditioned.apply(Eq[0])

    Eq << Probability.Eq.of.Ne_0.Eq.independence.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-07-16
