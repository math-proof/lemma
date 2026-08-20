from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(GreaterEqual)

    return GreaterEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove(proved=False)
def prove(Eq):
    x, a = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(GreaterEqual(f(x), g(x)), (x, a))

    
    


if __name__ == '__main__':
    run()

# created on 2020-05-21
# updated on 2023-03-25
