from util import *


@apply
def apply(given):
    return Unequal(*given.of(Greater))


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-12-08
