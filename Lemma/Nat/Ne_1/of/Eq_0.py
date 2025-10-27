from util import *


@apply
def apply(given, y):
    x = given.of(Equal[0])
    assert y.is_nonzero

    return Unequal(x, y)


@prove
def prove(Eq):
    a = Symbol(real=True, given=True)
    Eq << apply(Equal(a, 0), One())

    Eq << Eq[1].subs(Eq[0])

    
    


if __name__ == '__main__':
    run()
# created on 2018-03-20
# updated on 2025-04-20
