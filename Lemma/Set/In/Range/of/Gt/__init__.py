from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_integer or n.is_extended_integer
    return Element(n, Range(b + 1, oo))


@prove
def prove(Eq):
    from Lemma import Algebra

    n, b = Symbol(integer=True, given=True)
    Eq << apply(n > b)

    Eq << Eq[-1].simplify()

    Eq << Algebra.Ge.given.Gt.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-01

del Lt
del Gt
del Ge
del Le
from . import Lt
from . import Gt
from . import Ge
from . import Le
