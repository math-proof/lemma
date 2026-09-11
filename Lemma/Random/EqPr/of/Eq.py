from util import *


@apply(simplify=None)
def apply(given, *weights):
    lhs, rhs = given.of(Equal)
    assert lhs.is_random
    assert rhs.is_random
    return Equal(Pr(lhs, *weights), Pr(rhs, *weights))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(n))
    p, q = Symbol(shape=(n,), integer=True, random=True)
    θ = Symbol(real=True, shape=(n,))
    Eq << apply(Equal(p[i], q[i]))

    Eq << Eq[-1].simplify()





if __name__ == '__main__':
    run()

# created on 2020-12-13
# updated on 2023-04-05


