from util import *


@apply
def apply(self, pivot=-1, *, simplify=True):
    args, *limits = self.of(Sum[Mul])
    for i, (k, *ab) in enumerate(limits):
        if not ab:
            domain = self.expr.domain_defined(k)
            assert domain.is_Range
            limits[i] = k, *domain.args

    former, latter = std.array_split(args, pivot)
    former = Mul(*former)
    latter = Mul(*latter)

    former = Stack(former, *limits)
    latter = Stack(latter, *limits)
    if simplify:
        former = former.simplify()
        latter = latter.simplify()
    return Equal(self, former @ latter, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    y, x = Symbol(shape=(n,), real=True)
    Eq << apply(Sum[i:n](y[i] * x[i]))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.lhs.simplify()





if __name__ == '__main__':
    run()
# created on 2020-11-18
# updated on 2023-09-18

from . import arithmetic_progression
