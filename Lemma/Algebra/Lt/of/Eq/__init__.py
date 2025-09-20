from util import *


@apply
def apply(given, b):
    x, y = given.of(Equal)
    assert y < b
    return Less(x, b)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Equal(a, b), b + 1)

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-08-24


del Lt
from . import Lt
from . import relax
del Gt
from . import Gt
