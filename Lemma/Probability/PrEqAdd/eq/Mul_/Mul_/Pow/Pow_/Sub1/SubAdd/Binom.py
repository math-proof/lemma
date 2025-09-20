from util import *


@apply
def apply(X0, X1):
    n0, p = pspace(X0).distribution.of(BinomialDistribution)
    n1, S[p] = pspace(X1).distribution.of(BinomialDistribution)

    Y = Symbol(distribution=BinomialDistribution(n0 + n1, p))
    y = pspace(Y).symbol

    return Equal(Pr(Equal(X0 + X1, y)), Pr(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    n0, n1 = Symbol(integer=True, positive=True)
    p = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    X0 = Symbol(distribution=BinomialDistribution(n0, p))
    X1 = Symbol(distribution=BinomialDistribution(n1, p))
    Eq << apply(X0, X1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[0].subs(Eq[-1])

    Eq << Discrete.Pow.eq.Sum.Binom.Newton.apply((p + 1) ** n0, swap=True)

    Eq << Discrete.Pow.eq.Sum.Binom.Newton.apply((p + 1) ** n1, swap=True)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Discrete.Pow.eq.Sum.Binom.Newton.apply((p + 1) ** (n0 + n1), swap=True).subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Sum.as_multiple_limits)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, -Eq[-1].lhs.variables[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap.intlimit.parallel)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Tensor.Sum.eq.Dot)

    Eq << Tensor.Eq.of.EqDotSStack_Pow.independence.vector.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[0].lhs.arg.rhs)

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq[1].find(Sum).variable)

    Eq << Eq[-1] * Mul(*Eq[0].rhs.args[:-1])





if __name__ == '__main__':
    run()
# created on 2021-07-17
# updated on 2021-11-25
