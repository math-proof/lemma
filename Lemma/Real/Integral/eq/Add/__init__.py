from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Integral[Add])

    rhs = Add(*(Integral(arg, *limits) for arg in args))

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f, h = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x) + h(x)))


if __name__ == '__main__':
    run()

# created on 2020-06-05
from . import split
from . import by_parts
