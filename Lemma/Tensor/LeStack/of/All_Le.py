from util import *


@apply
def apply(given, *, simplify=True):
    (lhs, rhs), *limits = given.of(All[LessEqual])
    lhs = Stack(lhs, *limits)
    rhs = Stack(rhs, *limits)
    if simplify:
        lhs = lhs.simplify(squeeze=True)
        rhs = rhs.simplify(squeeze=True)
    return lhs <= rhs


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(All[i:n](f(i) <= g(i)))

    Eq << ~Eq[1]

    Eq << ~Eq[-1]

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-04-01
