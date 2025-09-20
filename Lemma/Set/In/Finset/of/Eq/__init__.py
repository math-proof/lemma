from util import *


@apply(simplify=False)
def apply(given):
    x, e = given.of(Equal)
    return Element(x, {e}, evaluate=False)


@prove
def prove(Eq):
    x, e = Symbol(integer=True)
    Eq << apply(Equal(x, e))

    Eq << Eq[1].simplify()






if __name__ == '__main__':
    run()
# created on 2018-10-23
del Eq
from . import Eq
