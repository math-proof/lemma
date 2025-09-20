from util import *


@apply
def apply(given):
    x, a = given.of(LessEqual)
    return Less(x, a)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(x <= a)

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]




if __name__ == '__main__':
    run()

# created on 2021-08-18
# updated on 2023-06-02
del One
from . import One
from . import relax
