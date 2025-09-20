from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)

    return Equal(sigmoid(lhs), sigmoid(rhs))


@prove
def prove(Eq):
    x = Symbol(real=True)
    f = Function(real=True)
    g = Function(real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-05-25
