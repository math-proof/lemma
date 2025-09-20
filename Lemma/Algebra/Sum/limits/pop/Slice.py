from util import *


def rewrite(Sum, self, index):
    expr, *limits = self.of(Sum)
    x, = limits[index]
    x, (start, stop) = x.of(Sliced)
    assert start <= stop - 1
    # allow empty slices in summation??
    limits[index] = x[stop - 1],
    limits.insert(index, x[start:stop - 1])
    return Sum(expr, *limits)

@apply
def apply(self, index=0):
    return Equal(self, rewrite(Sum, self, index))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.apply(Algebra.Sum.limits.concat)





if __name__ == '__main__':
    run()
# created on 2020-12-20
# updated on 2023-11-18
