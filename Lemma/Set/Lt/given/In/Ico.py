from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(Less)
    assert n.is_integer
    return Element(n, Range(-oo, b))


@prove
def prove(Eq):
    n, b = Symbol(integer=True, given=True)

    Eq << apply(n < b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2021-08-05
