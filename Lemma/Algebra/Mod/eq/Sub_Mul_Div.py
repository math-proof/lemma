from util import *


@apply
def apply(self):
    a, b = self.of(Mod)
    return Equal(self, a - a // b * b)


@prove(provable=False)
def prove(Eq):
    n, d = Symbol(integer=True)

    Eq << apply(n % d)


if __name__ == '__main__':
    run()
# created on 2018-02-25
