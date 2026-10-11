from util import *


@apply
def apply(ge, x, y, z):
    n = ge.of(Expr >= 3)
    return Unequal(x ** n + y ** n, z ** n)


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True)
    x, y, z = Symbol(integer=True, nonnegative=True)
    Eq << apply(n >= 3, x, y, z)


if __name__ == '__main__':
    run()
# created on 2021-08-26
