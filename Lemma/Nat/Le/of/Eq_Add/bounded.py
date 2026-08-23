from util import *


@apply
def apply(eq_add, index=0):
    args, a = eq_add.of(Equal[Add])
    assert all(arg >=0 for arg in args)
    return args[index] <= a


@prove
def prove(Eq):
    a, b, c = Symbol(real=True, nonnegative=True, given=True)
    d = Symbol(real=True, given=True)
    Eq << apply(Equal(a + b + c, d))

    Eq << ~Eq[1]

    Eq << Eq[-1] + (b + c)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-10-03
