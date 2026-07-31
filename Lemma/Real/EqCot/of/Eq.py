from util import *


@apply
def apply(given, *, simplify=True):
    lhs, rhs = given.of(Equal)
    lhs, rhs = cot(lhs), cot(rhs)
    if simplify:
        lhs, rhs = lhs.simplify(), rhs.simplify()
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(complex=True)
    Eq << apply(Equal(x, y))
    
    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2022-01-20
