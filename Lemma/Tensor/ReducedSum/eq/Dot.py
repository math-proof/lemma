from util import *


@apply
def apply(self):
    x, y = self.of(ReducedSum[Mul])

    n, = x.shape
    S[n], = y.shape
    rhs = x @ y

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y, x = Symbol(shape=(n,), real=True)
    Eq << apply(ReducedSum(x * y))

    Eq << Eq[0].this.lhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-16
