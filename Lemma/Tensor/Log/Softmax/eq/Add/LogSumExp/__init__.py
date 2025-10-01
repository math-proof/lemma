from util import *


@apply
def apply(self):
    x = self.of(log[softmax])
    n, = x.shape
    return Equal(self, x - logsumexp(x))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(log(softmax(x)))

    Eq << Eq[0].find(softmax).this.apply(Tensor.Softmax.eq.Mul.ReducedSum)

    Eq << Eq[-1].apply(Algebra.EqLogS.of.Eq)

    Eq << Eq[-1].this.rhs.apply(Algebra.Log.eq.Add)

    Eq << Eq[-1].this.find(Log[ReducedSum]).apply(Tensor.Log.ReducedSum.eq.LogSumExp)




if __name__ == '__main__':
    run()
# created on 2022-03-31

del Max
from . import Max
