from util import *


@apply(simplify=False)
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_random
    assert rhs.is_random
    return Equal(Pr(lhs), Pr(rhs))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    p, q = Symbol(shape=(n,), integer=True, random=True)
    Eq << apply(Equal(p[i], q[i]))

    Eq << Eq[-1].simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-03-23
