from util import *


@apply
def apply(x):
    n = x.generate_var(integer=True, var='n')
    return Equal(E ** x, Sum[n:oo](x ** n / factorial(n)))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)

    


if __name__ == '__main__':
    run()

# created on 2018-02-13
# updated on 2022-01-07