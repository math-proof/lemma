from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_finite
    return Element(n, Interval.open(b, oo))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)
    Eq << apply(n > b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2019-07-28
del Gt
del Lt
del Ge
from . import Gt
from . import average
from . import Lt
from . import Ge
