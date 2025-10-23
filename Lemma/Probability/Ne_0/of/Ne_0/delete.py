from util import *


@apply
def apply(given, index=-1):
    [*eqs] = given.of(Unequal[Pr[And], 0])

    del eqs[index]

    eq = And(*eqs)

    return Unequal(Pr(eq), 0)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus, Nat, Nat

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(x, y), 0))

    Eq.y_marginal_probability = Probability.Integral.eq.Pr.marginal.apply(Integral[y.var](Pr(x, y)))

    Eq << Nat.Gt_0.of.Ne_0.apply(Eq[0])

    Eq << Calculus.GtIntegral.of.All_Gt.apply(Eq[-1], (y.var,))

    Eq << Eq[-1].subs(Eq.y_marginal_probability)

    Eq <<= Nat.Ne.of.Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-12-12
# updated on 2023-04-28
