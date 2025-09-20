from util import *


@apply
def apply(eq, x):
    lhs, rhs = eq.of(Equal)
    assert lhs._has(x) and rhs._has(x)

    return Equal(Limit[x:0](lhs / x), Limit[x:0](rhs / x))


@prove
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Equal(f(x), g(x)), x)

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-05-02
