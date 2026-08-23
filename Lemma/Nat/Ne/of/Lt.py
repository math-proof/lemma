from util import *


@apply
def apply(given):
    return Unequal(*given.of(Less))


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-09-18
