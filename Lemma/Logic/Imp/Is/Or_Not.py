from util import *


@apply
def apply(self):
    p, q = self.of(Imply)
    return p.invert() | q


@prove(provable=False)
def prove(Eq):
    p, q = Symbol(bool=True)
    Eq << apply(Imply(p, q))

    


if __name__ == '__main__':
    run()
# created on 2018-01-01
# updated on 2022-01-27
