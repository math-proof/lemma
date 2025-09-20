from util import *


@apply
def apply(given):
    (expr, limit), x0 = given.of(Equal[ArgMax])
    return Equal(expr._subs(limit[0], x0), Maxima(expr, limit))


@prove(provable=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMax[x](f(x))))

    
    


if __name__ == '__main__':
    run()
# created on 2019-04-12
# updated on 2023-11-05
