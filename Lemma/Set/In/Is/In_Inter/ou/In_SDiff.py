from util import *


@apply
def apply(given, B):
    x, A = given.of(Element)

    return Or(Element(x, A - B), Element(x, A & B))


@prove
def prove(Eq):
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Element(x, A), B)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()


# created on 2018-02-21

