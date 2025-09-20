from util import *


@apply
def apply(given, x):
    lhs, rhs = given.of(Equal)

    return Equal(Max(lhs, x).simplify(), Max(rhs, x).simplify())


@prove
def prove(Eq):
    x, y, z = Symbol(real=True)

    Eq << apply(Equal(x, y), z)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-08-07
