from util import *


@apply
def apply(given, index=0):
    args, M = given.of(Equal[Max])
    return GreaterEqual(M, args[index])


@prove
def prove(Eq):
    M, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(M, Max(f(x), g(x))))

    Eq << GreaterEqual(Max(f(x), g(x)), f(x), plausible=True)
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2019-04-23
