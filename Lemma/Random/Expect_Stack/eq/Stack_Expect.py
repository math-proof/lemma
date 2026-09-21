from util import *


@apply
def apply(self):
    from Lemma.Random.Expect_Sum.eq.Sum_Expect import extract
    return Equal(self, extract(Stack, self))



@prove
def prove(Eq):
    from Lemma import Random, Real, Tensor

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Expectation(Stack[k:n](f(x[k])) | s))

    Eq << Eq[-1].this.lhs.apply(Random.Expect.eq.Integral_Mul_Prob)

    Eq << Eq[-1].this.find(Expectation).apply(Random.Expect.eq.Integral_Mul_Prob)

    Eq << Eq[-1].this.lhs.find(Mul).apply(Tensor.Mul_Stack.eq.Stack_Mul)

    Eq << Eq[-1].this.lhs.apply(Real.Integral_Stack.eq.Stack_Integral)

    Eq << Eq[-1].this.expr.rhs.find(Pr).apply(Random.All_Eq_Integral_ProbJoint.of.PSpace_Joint, x[k + 1:n])

    Eq << Eq[-1].this.find(And).apply(Tensor.Stack.UFn.Is.Stack)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Real.Mul_Integral.eq.Integral_Mul)

    Eq << Eq[-1].this.rhs.apply(Real.Integral_UFnProd.eq.Integral)

    Eq << Eq[-1].this.rhs.find(Pr).apply(Random.All_Eq_Integral_ProbJoint.of.PSpace_Joint, x[:k])

    Eq << Eq[-1].this.find(And).apply(Tensor.Stack.UFn.Is.Stack)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Real.Mul_Integral.eq.Integral_Mul)

    Eq << Eq[-1].this.rhs.apply(Real.Integral_UFnProd.eq.Integral)


if __name__ == '__main__':
    run()
# created on 2023-04-02
