from util import *


@apply
def apply(self):
    (x, (S[x], (S[x],))), (S[x],) = self.of(Variance[Expr - Expectation])
    return Equal(self, Variance[x](x))

@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Variance[x](x - Expectation(x)))

    Eq << Eq[0].lhs.this.apply(Probability.Var.eq.Expect)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.rhs.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[0].this.rhs.apply(Probability.Var.eq.Expect)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)



if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
