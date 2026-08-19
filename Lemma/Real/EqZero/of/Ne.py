from util import *


@apply
def apply(self, f, x):
    i, j = self.of(Unequal)
    return Equal(Derivative[x[i]](f(x[j])), Zeros(*x[j].shape, *x[i].shape))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    i, j = Symbol(integer=True)
    Eq << apply(Unequal(i, j), f, x)

    

    


if __name__ == '__main__':
    run()
# created on 2023-03-18
