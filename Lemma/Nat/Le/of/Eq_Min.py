from util import *


@apply
def apply(given, index=0):
    args, M = given.of(Equal[Min])
    return LessEqual(M, args[index])


@prove
def prove(Eq):
    M, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(M, Min(f(x), g(x))))

    Eq << LessEqual(Min(f(x), g(x)), f(x), plausible=True)
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2019-04-24
