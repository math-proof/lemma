from util import *


@apply
def apply(self):
    expr, *limits = self.of(Variance)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    return Equal(self,
                 Expectation(expr.outer_product(), *limits, given=given) - Expectation(expr, *limits, given=given).outer_product())

@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    x, t = Symbol(integer=True, random=True, shape=(n,))
    Eq << apply(Variance(x | t))

    Eq << Eq[-1].this.lhs.apply(Probability.Var.eq.Expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(Probability.Expect.eq.Mul)

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))

    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
# created on 2023-03-24
# updated on 2023-04-14
