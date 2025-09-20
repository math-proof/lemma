from util import *


@apply
def apply(self):
    x = self.of(Norm ** 2)
    n, = x.shape
    return Equal(self, Norm(x[:n - 1]) ** 2 + Abs(x[n - 1]) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x) ** 2)

    Eq << Eq[0].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Sub.push)


if __name__ == '__main__':
    run()
# created on 2023-06-24
