from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(LessEqual)
    assert n.is_finite
    return Element(n, Interval(-oo, b))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)
    Eq << apply(n <= b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2019-11-16

del Le
