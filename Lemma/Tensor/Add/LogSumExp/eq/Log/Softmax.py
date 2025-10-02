from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr - Log[ReducedSum[Exp]])
    n, = x.shape
    return Equal(self, log(softmax(x)))


@prove
def prove(Eq):
    from Lemma import Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x - Log(ReducedSum(Exp(x))))

    Eq << Eq[0].this.rhs.apply(Tensor.Log.Softmax.eq.Add.LogSumExp)


if __name__ == '__main__':
    run()
# created on 2022-03-31
