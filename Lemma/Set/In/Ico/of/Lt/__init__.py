from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Less)
    assert n.is_extended_integer
    return Element(n, Range(-oo, b))


@prove
def prove(Eq):
    n, b = Symbol(integer=True, given=True)
    Eq << apply(n < b)

    Eq << Eq[-1].simplify()




if __name__ == '__main__':
    run()

# created on 2018-02-28
# updated on 2023-11-13

del Le
del Lt
del Ge
del Gt
from . import Gt
from . import Le
from . import Lt
from . import Ge
