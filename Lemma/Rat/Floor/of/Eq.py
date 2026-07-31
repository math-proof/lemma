from util import *


@apply
def apply(given):
    x, y = given.of(Equal)

    return Equal(floor(x), floor(y))


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    Eq << apply(Equal(x, y))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-05-08
