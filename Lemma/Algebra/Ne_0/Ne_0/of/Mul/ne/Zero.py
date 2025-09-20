from util import *


@apply
def apply(given, index=-1):
    args = given.of(Unequal[Mul, 0])
    first = Mul(*args[:index])
    second = Mul(*args[index:])

    return Unequal(first, 0).simplify(), Unequal(second, 0).simplify()


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(a * b, 0))



    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2018-01-22

