from util import *


@apply
def apply(nonoverlapping, x_equal, i=None, j=None):
    a_cup_finiteset, n = nonoverlapping.of(Equal[Card])
    (xk, limit), S[a_cup_finiteset] = x_equal.of(Equal[Cup[FiniteSet]])
    x = Stack(xk, limit).simplify()
    S[n], = x.shape

    ak, limit = a_cup_finiteset.of(Cup[FiniteSet])
    a = Stack(ak, limit).simplify()
    S[n], = a.shape

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove(proved=False)
def prove(Eq):

    n = Symbol(domain=Range(2, oo))

    x, a = Symbol(shape=(oo,), integer=True)
    k = Symbol(integer=True)

    i, j = Symbol(domain=Range(n), given=True)

    Eq << apply(Equal(Card(a[:n].cup_finiteset(k)), n),
                Equal(x[:n].cup_finiteset(k), a[:n].cup_finiteset(k)),
                i=i, j=j)


if __name__ == '__main__':
    run()

# created on 2021-09-25
