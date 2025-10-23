from util import *


@apply
def apply(self, pivot=-1, *, simplify=True):
    args, *limits = self.of(Sum[Add])
    for i, (k, *ab) in enumerate(limits):
        if not ab:
            domain = self.expr.domain_defined(k)
            assert domain.is_Range
            limits[i] = k, *domain.args

    if isinstance(pivot, int):
        pivot = [pivot] * len(args)

    prod = []
    for pivot, s in zip(pivot, args):
        former, latter = std.array_split(s.of(Mul), pivot)
        former = Mul(*former)
        latter = Mul(*latter)

        former = Stack(former, *limits)
        latter = Stack(latter, *limits)
        if simplify:
            former = former.simplify()
            latter = latter.simplify()
        prod.append(former @ latter)
    return Equal(self, Add(*prod), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Finset, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b, y, x = Symbol(shape=(n,), real=True)
    Eq << apply(Sum[i:n](y[i] * x[i] + a[i] * b[i]))

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)


if __name__ == '__main__':
    run()
# created on 2023-09-18
