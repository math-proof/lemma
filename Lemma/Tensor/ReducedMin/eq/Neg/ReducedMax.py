from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedMin)
    return Equal(self, -ReducedMax(-expr))




@prove
def prove(Eq):
    from Lemma import Real, Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(ReducedMin(x[:n]))

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedMin.eq.Minima)

    Eq << Eq[-1].this.find(ReducedMax).apply(Tensor.ReducedMax.eq.Maxima)

    Eq << Eq[-1].this.find(Maxima).apply(Real.Maxima.eq.Neg.Minima)


if __name__ == '__main__':
    run()
# created on 2023-11-12
