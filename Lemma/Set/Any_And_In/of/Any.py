from util import *


@apply
def apply(given):
    expr, (lhs, *rhs) = given.of(Any)
    if len(rhs) == 2:
        rhs = lhs.range(*rhs)
    else:
        rhs, = rhs

    return Any[lhs]((expr & Element(lhs, rhs)).simplify())


@prove
def prove(Eq):
    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(Any[e:S](f(e) > 0))

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-02-15

