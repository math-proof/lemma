from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(Greater)

    return Element(n, Interval.open(b, oo))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)

    Eq << apply(n > b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2021-09-23
