from util import *


def rewrite(Sum, self, index):
    expr, *limits = self.of(Sum)
    x, = limits[index]
    x, (start, stop) = x.of(Sliced)
    assert start + 1 < stop
    limits[index] = x[start + 1:stop],
    limits.insert(index, x[start])
    return Sum(expr, *limits)

@apply
def apply(self, index=0):
    return Equal(self, rewrite(Sum, self, index))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]](f(x[i:n])))

    
    


if __name__ == '__main__':
    run()

# created on 2020-03-18
# updated on 2023-03-27
