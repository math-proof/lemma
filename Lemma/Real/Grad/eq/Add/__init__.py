from util import *


@apply
def apply(self, *, simplify=True):
    args, *limits_d = self.of(Derivative[Add])

    args = [Derivative(arg, *limits_d) for arg in args]
    if simplify:
        args = [arg.doit() for arg in args]

    if len(self.expr.shape) < len(self.shape):
        for i, arg in enumerate(args):
            if len(arg.shape) < len(self.shape):
                args[i] *= Ones(*self.shape)
                args[i] = args[i].T

    return Equal(self, Add(*args))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) + g(x)))




if __name__ == '__main__':
    run()

# created on 2020-04-20
# updated on 2023-03-29

from . import Leibneiz
