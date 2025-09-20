from util import *


@apply
def apply(self):
    x = self.of(ReducedSum[Softmax])

    return Equal(self, Ones(*x.shape[:-1]))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(m, n), real=True)
    Eq << apply(ReducedSum(Softmax(x)))

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Tensor.Sum.eq.Stack)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)






if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-05-06
