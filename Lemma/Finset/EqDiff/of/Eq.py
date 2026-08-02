from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    lhs = Difference(lhs, *limits)
    rhs = Difference(rhs, *limits)
    return Equal(lhs, rhs)

@prove
def prove(Eq):
    d = Symbol(integer=True, positive=True)
    x = Symbol(integer=True)
    f, g = Function(shape=(), complex=True)
    Eq << apply(Equal(f(x), g(x)), (x, d))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-10-09
