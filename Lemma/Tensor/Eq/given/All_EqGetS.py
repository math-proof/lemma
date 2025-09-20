from util import *


@apply
def apply(self, i=None):
    x, y = self.of(Equal)
    assert x.shape == y.shape

    if isinstance(i, (tuple, Tuple, list)):
        shape = x.shape
        for i_, n in zip(i, shape):
            assert i_.domain == Range(n)
    else:
        n = x.shape[0]
        assert i.domain == Range(n)

    return Equal(x[i], y[i])


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True, given=True)
    a, b = Symbol(shape=(n,), etype=dtype.integer)
    i = Symbol(domain=Range(n))
    Eq << apply(Equal(a, b), i=i)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[1], (i,))





if __name__ == '__main__':
    run()

# created on 2018-04-03
# updated on 2021-11-26
