from util import *


@apply
def apply(eq_0, eq_1, axis=0):
    x0, y0 = eq_0.of(Equal)
    x1, y1 = eq_1.of(Equal)
    
    return Equal(BlockMatrix[axis](x0, x1).simplify(), BlockMatrix[axis](y0, y1).simplify())


@prove
def prove(Eq):
    n, m, k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n, m))
    a, b = Symbol(real=True, shape=(k, m))
    Eq << apply(Equal(x, y), Equal(a, b))

    Eq << Eq[-1].subs(Eq[0], Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2022-01-13
