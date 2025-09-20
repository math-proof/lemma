from util import *


@apply
def apply(self):
    x = self.of(Tanh)

    rhs = Sinh(x) / Cosh(x)
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(tanh(x))


if __name__ == '__main__':
    run()
# created on 2023-11-26

del Add
from . import Add
