from util import *


@apply
def apply(given):
    x, a = given.of(Unequal)
    assert a.is_nonzero
    return Equal(x, 0)


@prove
def prove(Eq):
    n = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 1))

    Eq << Eq[0].subs(Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2023-05-22
