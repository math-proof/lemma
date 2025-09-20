from util import *


@apply(simplify=None)
def apply(given, axis=(-2, 1)):
    lhs, rhs = given.of(Equal)
    return Equal(Transpose[axis](lhs), Transpose[axis](rhs))


@prove
def prove(Eq):
    x = Symbol(complex=True)
    n, m = Symbol(integer=True, positive=True)
    f, g = Function(complex=True, shape=(n, n, m))
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2022-01-11
