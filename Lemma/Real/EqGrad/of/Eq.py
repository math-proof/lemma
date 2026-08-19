from util import *


@apply
def apply(given, *limits, simplify=False):
    lhs, rhs = given.of(Equal)

    limits = [x for x, *_ in limits]

    lhs = Derivative(lhs, *limits) 
    rhs = Derivative(rhs, *limits)
    if simplify:
        rhs = rhs.simplify()
        lhs = lhs.simplify()
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(f(x), g(x)), (x,))

    Eq << Eq[1].subs(Eq[0])

    
    


if __name__ == '__main__':
    run()

# created on 2020-10-17
# updated on 2021-11-25