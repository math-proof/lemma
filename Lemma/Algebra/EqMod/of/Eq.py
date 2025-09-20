from util import *


@apply
def apply(given, divisor=None):
    lhs, rhs = given.of(Equal)
    divisor = sympify(divisor)
    assert divisor > 0 and divisor.is_integer
    assert lhs.is_integer or rhs.is_integer
    return Equal(lhs % divisor, rhs % divisor)


@prove
def prove(Eq):
    x, y = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Equal(x, y), d)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-11-22
