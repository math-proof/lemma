from util import *


@apply
def apply(self):
    x = self.of(csch)
    return Equal(self, sinh(x) ** -1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(csch(x))


if __name__ == '__main__':
    run()
# created on 2023-11-26
