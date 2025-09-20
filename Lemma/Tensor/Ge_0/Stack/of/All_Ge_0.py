from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Expr >= 0])
    shape = given.limits_shape
    
    return Stack(lhs, *limits) >= Zeros(*shape, *lhs.shape)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(All[i:n](f(i) >= 0))
    
    Eq << ~Eq[1]
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-01-01
