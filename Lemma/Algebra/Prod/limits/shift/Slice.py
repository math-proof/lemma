from util import *


@apply
def apply(self, index=0):
    from Lemma.Algebra.Sum.limits.shift.Slice import rewrite
    return Equal(self, rewrite(Product, self, index))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Product[x[i:n + 1]](f(x[i:n + 1])))






if __name__ == '__main__':
    run()
# created on 2023-11-18
