from util import *


@apply
def apply(self):
    x = self.of(log[softmax])
    n, = x.shape
    return Equal(self, x - Log(ReducedSum(Exp(x))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(log(softmax(x)))

    Eq << Eq[0].find(softmax).this.apply(Tensor.Softmax.eq.Div_SumExp)

    Eq << Logic.EqUFnS.of.Eq.apply(Eq[-1], log)

    Eq << Eq[-1].this.rhs.apply(Real.LogMul.eq.AddLogS)


if __name__ == '__main__':
    run()
# created on 2022-03-31

