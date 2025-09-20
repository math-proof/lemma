from util import *


@apply
def apply(given):
    expr, *limits = given.of(Any)
    return Any[given.variables](And(expr, given.limits_cond).simplify())


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f = Function(shape=(), integer=True)

    Eq << apply(Any[x:A, y:B](f(x, y) > 0))

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()


# created on 2018-03-06
