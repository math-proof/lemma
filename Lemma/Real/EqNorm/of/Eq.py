from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(Norm(lhs), Norm(rhs), evaluate=False)


@prove
def prove(Eq):
    x = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(complex=True, shape=(n,))
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-10-02
