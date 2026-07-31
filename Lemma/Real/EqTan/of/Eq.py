from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(tan(lhs), tan(rhs))


@prove
def prove(Eq):
    x, y = Symbol(complex=True)
    Eq << apply(Equal(x, y))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-09-27
