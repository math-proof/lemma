from util import *


@apply
def apply(given, *, simplify=True):
    lhs, rhs = given.of(Equal)

    lhs, rhs = ReducedSum(lhs), ReducedSum(rhs)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    assert i.is_integer
    f, g = Function(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-08-26
