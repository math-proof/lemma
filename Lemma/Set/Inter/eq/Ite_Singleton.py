from util import *


@apply
def apply(e, s):
    return Equal(s & e.set, Piecewise((e.set, Element(e, s)), (e.emptySet, True)))


@prove
def prove(Eq):
    s = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)

    Eq << apply(e, s)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()

# created on 2020-08-24
