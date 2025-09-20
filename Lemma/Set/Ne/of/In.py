from util import *


@apply
def apply(given):
    x, complement = given.of(Element)
    U, y = complement.of(Complement)
    y = y.of(FiniteSet)
    return Unequal(x, y)

@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    x, y = Symbol(complex=True, shape=(n,), given=True)
    C = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, C - {y}))

    Eq << ~Eq[1]

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-17
