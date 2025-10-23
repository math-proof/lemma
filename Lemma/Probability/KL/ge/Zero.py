from util import *


@apply
def apply(self):
    assert self.is_KL
    return GreaterEqual(self, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Finset, Finset

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(KL(Pr[θ](x), Pr[θ_quote](x)))

    Eq << Eq[-1].this.find(KL).apply(Probability.KL.eq.Sum)

    Eq << Algebra.Log.ge.Sub_.One.Inv.apply(Eq[1].find(Log).arg)

    Eq << Algebra.GeMul.of.Ge.apply(Eq[-1], Eq[1].find(Pr))

    x = Eq[1].lhs.variable
    Eq << Algebra.GeSum.of.Ge.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Probability.Sum.eq.One)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Probability.Sum.eq.One)





if __name__ == '__main__':
    run()

# created on 2021-07-20
# updated on 2023-04-22
