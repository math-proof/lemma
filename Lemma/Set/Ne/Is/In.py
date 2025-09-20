from util import *


@apply
def apply(x, y):
    return Iff(Unequal(x, y), Element(x, y.universalSet - {y}))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(complex=True, shape=(n,), given=True)

    Eq << apply(x, y)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()

# created on 2021-08-16
