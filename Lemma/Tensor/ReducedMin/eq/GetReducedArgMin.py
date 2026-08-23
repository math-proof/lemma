from util import *


@apply
def apply(self):
    return Equal(ReducedMin(self), self[ReducedArgMin(self)])


@prove
def prove(Eq):
    from Lemma import Tensor

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    y = Symbol(-x)
    Eq.y_def = y.this.definition

    Eq << -Eq.y_def.reversed

    Eq << Eq[0].subs(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedMin.eq.Neg.ReducedMax)

    Eq << Eq[-1].this.find(ReducedArgMin).apply(Tensor.ReducedArgMin.eq.ReducedArgMax.Neg)

    Eq << Tensor.ReducedMax.eq.GetReducedArgMax.apply(y[:n])




if __name__ == '__main__':
    run()
# created on 2023-11-12
