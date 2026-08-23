from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr <= 0)
    return LessEqual(x, y)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)
    
    Eq << apply(LessEqual(a - b, 0))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2022-04-01
