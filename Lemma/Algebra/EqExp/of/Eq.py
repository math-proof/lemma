from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    f, g = Function(shape=(), real=True)

    Eq << apply(Equal(f(i), g(i)))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-08-26
