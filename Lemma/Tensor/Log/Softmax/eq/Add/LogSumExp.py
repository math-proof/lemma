from util import *


@apply
def apply(self):
    x = self.of(log[softmax])
    n, = x.shape
    return Equal(self, x - Log(ReducedSum(Exp(x))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Bool, Real

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(log(softmax(x)))

    Eq << Eq[0].find(softmax).this.apply(Tensor.Softmax.eq.DivExp_KeepdimSumExp)

    Eq << Bool.EqUFnS.of.Eq.apply(Eq[-1], log)

    Eq << Eq[-1].this.rhs.apply(Real.LogMul.eq.AddLogS.of.Ne_0.Ne_0)


if __name__ == '__main__':
    run()
# created on 2022-03-31

