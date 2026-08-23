from util import *


@apply
def apply(given, var=None):
    arg, m = given.of(Equal[ReducedArgMax])
    k = arg.generate_var(integer=True, var=var)
    n, = arg.shape
    return All[k:m](arg[m] > arg[k])


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    M = Symbol(integer=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedArgMax(f(x))))

    


if __name__ == '__main__':
    run()
# created on 2023-11-05
