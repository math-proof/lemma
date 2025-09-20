from util import *


@apply
def apply(given):
    contains, *limits = given.of(Any)
    x, B = contains.of(Element)
    return Unequal(B, B.etype.emptySet)


@prove
def prove(Eq):

    A = Symbol(etype=dtype.real)
    B = Symbol(etype=dtype.real, given=True)
    e = Symbol(real=True)

    Eq << apply(Any[e:A](Element(e, B)))

    Eq << ~Eq[-1]

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-12-24
