from util import *

@apply
def apply(self):
    x = Symbol(shape=(oo,), etype=dtype.integer)
    assert x.type.slice(0) == dtype.integer.set
    assert not x.is_set

    n, k = self.of(Stirling1)
    i = Symbol(integer=True)

    condSet = conditionset(x[:k],
                           And(Equal(Cup(x[i], (i, 0, k)), Range(n)),
                               Equal(Sum(Card(x[i]), (i, 0, k)), n),
                               All(Greater(Card(x[i]), 0), (i, 0, k))))

    return Equal(self, Card(imageset(x[:k], Cup(FiniteSet(x[i]), (i, 0, k)), condSet)))


@prove(provable=False)
def prove(Eq):

    n, k = Symbol(integer=True, positive=True)
    Eq << apply(Stirling1(n, k))


if __name__ == '__main__':
    run()
# created on 2021-09-06
