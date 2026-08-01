from util import *


@apply
def apply(eq, f_eq):
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = f_eq.of(Equal)
    return Equal(_lhs + lhs, _rhs + rhs)


@prove
def prove(Eq):
    a, b, x, y = Symbol(real=True)


    Eq << apply(Equal(a, b), Equal(x, y))

    Eq << Eq[1] + Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-05-09
