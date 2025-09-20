from util import *


@apply
def apply(self):
    args, (x_var, *ab) = self.of(Integral[Pr[Equal]])
    if args[-1].is_Tuple:
        (x, S[x_var]), *weights = args
    else:
        x, S[x_var] = args

    if ab:
        S[-oo], S[oo] = ab

    return Equal(self, 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True, random=True)
    x_ = Symbol('x', real=True)
    Eq << apply(Integral[x_](Pr(x)))


if __name__ == '__main__':
    run()
# created on 2021-08-24

del Conditioned
from . import Conditioned
