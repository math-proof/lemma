from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])
    return Unequal(x, y)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)

    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << ~Eq[-1]

    Eq << Eq[0].subs(Eq[-1])

if __name__ == '__main__':
    run()

# created on 2020-08-27
