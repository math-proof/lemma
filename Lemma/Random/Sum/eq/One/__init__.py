from util import *


@apply
def apply(self):
    args, (x_var, *_) = self.of(Sum[Pr[Equal[Symbol, Symbol]]])
    if args[-1].is_Tuple:
        (x, S[x_var]), *weights = args
    else:
        x, S[x_var] = args

    return Equal(self, 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(integer=True, random=True)
    Eq << apply(Sum[x.var](Pr(x)))




if __name__ == '__main__':
    run()
# created on 2021-07-19
# updated on 2023-03-25
del Conditioned
from . import Conditioned
