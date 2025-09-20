from util import *


@apply
def apply(given, rhs=None):
    x, y = given.of(Equal)
    return Equal(x @ rhs, y @ rhs)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    X, Y = Symbol(real=True, shape=(n, n))
    t = Symbol(real=True, shape=(n,))
    Eq << apply(Equal(X, Y), t)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-10-04
