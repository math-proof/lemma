from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(GreaterEqual)
    assert n.is_integer
    return Element(n, Range(b, oo))


@prove
def prove(Eq):
    n, b = Symbol(integer=True, given=True)
    Eq << apply(n >= b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2018-02-28

del Gt
del Lt
del Le
del Ge
from . import Gt
from . import Lt
from . import Le
from . import Ge
