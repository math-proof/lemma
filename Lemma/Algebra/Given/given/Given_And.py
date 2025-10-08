from util import *


@apply(simplify=False)
def apply(suffice, *, cond=None):
    cond = sympify(cond)
    fy, rhs = suffice.of(Given)
    return Given(fy, cond & rhs), cond


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Bool

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Given(Equal(a, 0), Equal(c, 0)), cond=Equal(b, 0))

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-03-03
