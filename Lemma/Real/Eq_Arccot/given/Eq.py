from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal[acot, acot])
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(complex=True)
    Eq << apply(Equal(acot(x), acot(y)))
    
    Eq << Eq[0].subs(Eq[1])


if __name__ == '__main__':
    run()
# created on 2022-01-23
