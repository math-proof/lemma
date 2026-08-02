from util import *

@apply
def apply(self):
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    assert x.type.slice(0) == dtype.integer.set
    assert not x.is_set
    n, k = self.of(Stirling)
    i = Symbol('i', integer=True)

    return Equal(self, Card(imageset(x[:k], Cup[i:k](FiniteSet(x[i])), self.conditionset(n, k, x))))


@prove(provable=False)
def prove(Eq):

    n, k = Symbol(integer=True, positive=True)
    Eq << apply(Stirling(n, k))


if __name__ == '__main__':
    run()
# created on 2020-10-04
