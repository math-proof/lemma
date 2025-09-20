from util import *


@apply
def apply(eq, lower=None, upper=None):
    lhs, rhs = eq.of(Equal)
    if upper is None:
        if lower < rhs:
            return lhs > lower
        elif lhs < upper:
            return rhs > lower
    else:
        if rhs < upper:
            return upper > lhs
        elif lhs < upper:
            return upper > rhs


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Equal(a, b), upper=b + 1)
    
    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-12-27
