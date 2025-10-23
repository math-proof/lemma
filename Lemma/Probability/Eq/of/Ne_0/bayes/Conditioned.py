from util import *


@apply
def apply(eq, *vars):
    given_probability = eq.of(Unequal[0])
    cond, given = given_probability.of(Pr[Conditioned])

    condition = And(*(Equal(var, pspace(var).symbol) for var in vars))
    return Equal(Pr(cond & condition, given=given), given_probability * Pr(condition, given=cond & given))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Nat, Nat, Nat, Nat

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(y | z), 0), x)

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-1], x, y)

    Eq.lhs = Nat.EqDivS.of.Eq.apply(Eq[-2], Eq[-1])

    Eq << Probability.Ne_0.of.Ne_0.joint.apply(Eq[0])

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-1], x)

    Eq << Nat.EqDivS.of.Eq.apply(Eq[-2], Eq[-1]).reversed

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[2], y)

    Eq << Nat.EqDivS.of.Eq.apply(Eq[2], Eq[-1]).reversed

    Eq << Eq[-1] * Eq[-3]

    Eq << Eq[-1].subs(Eq.lhs).reversed




if __name__ == '__main__':
    run()
# created on 2020-12-11

# updated on 2023-04-05
