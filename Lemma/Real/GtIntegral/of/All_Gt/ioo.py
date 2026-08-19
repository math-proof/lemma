from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])

    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](Greater(f(x), g(x))))


if __name__ == '__main__':
    run()

# created on 2019-01-28
