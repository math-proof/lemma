from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs > 0 or rhs > 0

    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    f = Function(shape=(), positive=True)
    g = Function(shape=(), real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    Eq << Greater(f(x), 0, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Algebra.Ne.of.Gt.apply(Eq[-1])

    


if __name__ == '__main__':
    run()

# created on 2018-08-04
# updated on 2025-04-20
