from util import *


@apply
def apply(given, a, i=None):
    x, y = given.of(Equal)
    assert x.shape == y.shape
    if i is None:
        return Equal(a[x], a[y])
    n = x.shape[0]
    return Equal(Stack[i:n](a[x[i]]), Stack[i:n](a[y[i]]))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(shape=(n,), integer=True)
    a = Symbol(shape=(n,), etype=dtype.integer)
    i = Symbol(integer=True)

    Eq << apply(Equal(x, y), a, i=i)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-08-26
