from util import *


@apply
def apply(eq, f_eq, swap=False):
    if swap:
        eq, f_eq = f_eq, eq
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = f_eq.of(Equal)
    return Equal(lhs - _lhs, rhs - _rhs)


@prove
def prove(Eq):
    a, b, x, y = Symbol(real=True)
    Eq << apply(Equal(a, b), Equal(x, y))

    Eq << Eq[0] - Eq[1]

    


if __name__ == '__main__':
    run()
# created on 2020-05-09
# updated on 2023-05-18
