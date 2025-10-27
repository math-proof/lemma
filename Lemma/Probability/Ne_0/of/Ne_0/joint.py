from util import *


# given: Pr(x | y) != 0
# imply: Pr(x, y) != 0
@apply
def apply(given):
    lhs, rhs = given.of(Unequal[Pr[Conditioned], 0])
    return Unequal(Pr(lhs, rhs), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Rat, Nat

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(x | y), 0))

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-1], x)

    Eq << Nat.Mul.ne.Zero.of.Ne_0.Ne_0.apply(Eq[0], Eq[2])

    Eq << Eq[-1].subs(Eq[-2].reversed)




if __name__ == '__main__':
    run()
# created on 2020-12-11
# updated on 2023-04-05
