from util import *


@apply
def apply(self):
    x = self.of(sec)
    return Equal(self, cos(x) ** -1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(sec(x))


if __name__ == '__main__':
    run()
# created on 2023-10-03
