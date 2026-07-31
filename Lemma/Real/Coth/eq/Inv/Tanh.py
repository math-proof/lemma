from util import *


@apply
def apply(self):
    x = self.of(coth)
    return Equal(self, 1 / tanh(x))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(coth(x))


if __name__ == '__main__':
    run()
# created on 2023-11-26
