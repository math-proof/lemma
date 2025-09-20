from util import *


@apply
def apply(given, divisor=None):
    lhs, rhs = given.of(Equal)
    divisor = sympify(divisor)
    assert divisor.is_nonzero
    return Equal(lhs / divisor, rhs / divisor, evaluate=False)


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    d = Symbol(real=True, zero=False)
    Eq << apply(Equal(x, y), d)

    Eq << Eq[-1].subs(Eq[0])




if __name__ == '__main__':
    run()

# created on 2018-05-24
# updated on 2023-04-18




del Gt
from . import Gt
from . import transplant
del Lt
from . import Lt
