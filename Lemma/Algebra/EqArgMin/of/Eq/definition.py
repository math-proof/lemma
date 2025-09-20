from util import *


@apply
def apply(given):
    (expr, limit), x0 = given.of(Equal[ArgMin])
    return Equal(expr._subs(limit[0], x0), Minima(expr, limit))


@prove(provable=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(x0, ArgMin[x](f(x))))

    
    


if __name__ == '__main__':
    run()
# created on 2019-04-13
# updated on 2023-11-05
