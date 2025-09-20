from util import *


@apply
def apply(self):
    expr = self.of(ReducedSum)
    *rest, axis = self.axis
    if len(rest) == 1:
        rest, = rest
    return Equal(self, ReducedSum[rest](ReducedSum[axis](expr)))

@prove(provable=False)
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(m, n))
    Eq << apply(ReducedSum[0, 1](x))

    


if __name__ == '__main__':
    run()
# created on 2023-12-17
