from util import *


@apply
def apply(x):
    n, = x.shape
    return Equal(log(softmax(x)), x - ReducedMax(x) - logsumexp(x - ReducedMax(x)))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x)

    Eq << Tensor.nn.Softmax.translation.apply(x, -ReducedMax(x)).reversed

    Eq << Eq[-1].apply(Algebra.EqLog.of.Eq)

    Eq << Eq[-1].this.rhs.arg.apply(Tensor.Softmax.eq.Mul.ReducedSum)

    Eq << Eq[-1].this.find(Log[ReducedSum]).apply(Tensor.Log.ReducedSum.eq.LogSumExp)



if __name__ == '__main__':
    run()
# created on 2021-01-06
# updated on 2022-03-31
