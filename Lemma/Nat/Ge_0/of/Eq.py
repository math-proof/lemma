from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    if rhs >= 0 or rhs.is_nonnegative:
        x = lhs
    elif lhs >= 0 or lhs.is_nonnegative:
        x = rhs

    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(nonnegative=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2021-09-10
# updated on 2023-10-15
