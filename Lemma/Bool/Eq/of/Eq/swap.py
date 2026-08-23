from util import *


@apply
def apply(given, x, y):
    given.of(Equal)

    d = Dummy(**y.type.dict)
    this = given._subs(x, d)
    this = this._subs(y, x)
    return this._subs(d, y)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i, j = Symbol(integer=True)
    x, y, z = Symbol(shape=(n,), real=True)

    Eq << apply(Equal(x @ y, Sum[j:n, i:n](KroneckerDelta(i, j) * x[j] * y[i])), x, y)

    Eq << Eq[0].subs(x, z)

    Eq << Eq[-1].subs(y, x)

    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    run()

# created on 2021-01-03
