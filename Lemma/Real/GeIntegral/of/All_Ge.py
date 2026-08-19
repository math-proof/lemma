from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    return GreaterEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](GreaterEqual(f(x), g(x))))


if __name__ == '__main__':
    run()

# created on 2019-01-25
