from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Less(x - y, Zeros(*x.shape))


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0] - y




if __name__ == '__main__':
    run()
# created on 2019-06-26
# updated on 2023-03-25

del Gt
from . import Gt
from . import trans
