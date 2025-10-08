from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_nonzero or rhs.is_nonzero
    return Equal(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True, given=True)
    a = Symbol(real=True, given=True)
    b = Symbol(real=True, zero=False, given=True)
    Eq << apply(Equal(x * a, b))

    Eq << Eq[-1].subs(Eq[0])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq << Eq[0].subs(Eq[-2])

    Eq << Eq[0].subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2021-08-16
# updated on 2023-04-05
