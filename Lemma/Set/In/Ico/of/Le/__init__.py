from util import *


@apply
def apply(given):
    n, b = given.of(LessEqual)

    assert n.is_integer
    return Element(n, Range(-oo, b + 1))


@prove
def prove(Eq):
    from Lemma import Algebra
    n, b = Symbol(integer=True, given=True)

    Eq << apply(n <= b)

    Eq << Eq[-1].simplify()

    Eq << Algebra.Lt.given.Le.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-05-21

del Ge
del Gt
del Le
del Lt
from . import Lt
from . import Ge
from . import Gt
from . import Le
