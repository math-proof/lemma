from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert not x.shape
    return Equal(self, Piecewise((0, Equal(x, 0)), (x / abs(x), True)))


@prove(provable=False)
def prove(Eq):
    
    z = Symbol(complex=True)
    Eq << apply(Sign(z))


if __name__ == '__main__':
    run()
# created on 2023-05-25
