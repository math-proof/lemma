from util import *


@apply
def apply(self):
    x = self.of(Softmax)
    return Equal(self, exp(x) / ReducedSum(exp(x)))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)

    Eq << apply(softmax(x))

    y = Symbol(softmax(x))

    i = Symbol(integer=True)

    Eq << y[i].this.definition

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()
# created on 2020-12-28
