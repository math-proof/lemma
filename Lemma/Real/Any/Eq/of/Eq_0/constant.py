from util import *


@apply
def apply(given):
    dfx = given.of(Equal[0])
    fx, *limits = dfx.of(Derivative)
    C = given.generate_var(real=True, var='C')
    return Any[C](All(Equal(fx, C), *((x,) for x,*_ in limits)))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f = Function(real=True)

    Eq << apply(Equal(Derivative[x](f(x)), 0))


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-06-12
