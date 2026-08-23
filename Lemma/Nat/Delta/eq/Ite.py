from util import *


@apply
def apply(self, swap=False):
    x, y = self.of(KroneckerDelta)
    if swap:
        x, y = y, x
    return Equal(self, Piecewise((1, Equal(x, y)), (0, True)))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(integer=True)
    Eq << apply(KroneckerDelta(x, y))

    


if __name__ == '__main__':
    run()
# created on 2019-04-20
# updated on 2023-05-22
