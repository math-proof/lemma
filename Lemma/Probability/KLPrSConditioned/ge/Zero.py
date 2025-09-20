from util import *


@apply
def apply(prob_lhs, prob_rhs):
    (x_eq, y_eq), *weights_lhs = prob_lhs.of(Pr[Conditioned])
    (S[x_eq], S[y_eq]), *weights_rhs = prob_rhs.of(Pr[Conditioned])
    return GreaterEqual(KL(prob_lhs, prob_rhs), 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    y = Symbol(random=True, integer=True, shape=(n,))
    Eq << apply(Pr[θ](x | y), Pr[θ_quote](x | y))

    Eq << Eq[0].this.find(KL).apply(Probability.KL.eq.Sum)

    Eq << Algebra.Log.ge.Sub_.One.Inv.apply(Eq[1].find(Log).arg)

    Eq << Algebra.GeMul.of.Ge.apply(Eq[-1], Eq[1].find(Pr))

    Eq << Algebra.GeSum.of.Ge.apply(Eq[-1], (x.var,))

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Probability.Sum.eq.One.Conditioned)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Probability.Sum.eq.One.Conditioned)





if __name__ == '__main__':
    run()
# created on 2021-07-19
# updated on 2023-03-26
