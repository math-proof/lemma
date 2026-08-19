from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)

    return Less(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(Less(f(x), g(x)), (x, -oo, oo))


if __name__ == '__main__':
    run()

# created on 2021-08-13
