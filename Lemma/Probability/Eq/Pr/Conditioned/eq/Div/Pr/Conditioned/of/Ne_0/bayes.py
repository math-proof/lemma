from util import *


@apply
def apply(given, index=-1):
    eqs = given.of(Unequal[Pr[And], 0])

    if eqs[-1].is_Tuple:
        eqs, *weights = eqs
    else:
        weights = []

    lhs, rhs = std.array_split(eqs, index)
    lhs = And(*lhs)
    rhs = And(*rhs)
    return Equal(Pr(lhs, *weights, given=rhs), Pr(rhs, *weights, given=lhs) * Pr(lhs, *weights) / Pr(rhs, *weights))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Nat

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(x, y), 0))

    Eq << Probability.And.Ne_0.of.Ne_0.apply(Eq[0])

    Eq <<= Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-2], y), Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[-1], x)

    Eq << Nat.Eq_Div.of.Eq.Ne_0.apply(Eq[-1], Eq[-3]).reversed

    Eq << Eq[-1].subs(Eq[-3])




if __name__ == '__main__':
    run()
# created on 2024-06-18
# updated on 2024-06-20
