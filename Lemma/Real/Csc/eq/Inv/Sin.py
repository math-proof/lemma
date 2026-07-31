from util import *


@apply
def apply(self):
    x = self.of(csc)
    return Equal(self, sin(x) ** -1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(csc(x))


if __name__ == '__main__':
    run()
# created on 2023-10-03
