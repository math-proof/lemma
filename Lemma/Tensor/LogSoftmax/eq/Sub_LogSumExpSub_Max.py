from util import *


@apply
def apply(x):
    n, = x.shape
    return Equal(log(softmax(x)), x - ReducedMax(x) - logsumexp(x - ReducedMax(x)))


@prove
def prove(Eq):
    from Lemma import Tensor, Logic

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(x)

    Eq << Tensor.SoftmaxAdd.eq.Softmax.apply(x, -ReducedMax(x)).reversed

    Eq << Logic.EqUFnS.of.Eq.apply(Eq[-1], log)

    Eq << Eq[-1].this.rhs.arg.apply(Tensor.Softmax.eq.Div_SumExp)

    Eq << Eq[-1].this.find(Log[ReducedSum]).apply(Tensor.LogSumExp.definition)


if __name__ == '__main__':
    run()
# created on 2021-01-06
# updated on 2022-03-31
