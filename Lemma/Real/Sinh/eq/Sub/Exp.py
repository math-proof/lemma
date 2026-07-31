from util import *


@apply
def apply(self):
    x = self.of(Sinh)
    return Equal(self, (Exp(x) - Exp(-x)) / 2, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(sinh(x))

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
