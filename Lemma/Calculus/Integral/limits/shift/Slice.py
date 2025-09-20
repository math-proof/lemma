from util import *


@apply
def apply(self, index=0):
    from Lemma.Algebra.Sum.limits.shift.Slice import rewrite
    return Equal(self, rewrite(Integral, self, index))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Integral[x[i:n]](f(x[i:n])))


if __name__ == '__main__':
    run()
# created on 2023-03-27
