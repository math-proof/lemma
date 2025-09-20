from util import *


@apply
def apply(eq):
    args = eq.of(Equal)
    return LessEqual(*args)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-04-22



from . import relax
del Le
from . import Le
del Ge
from . import Ge
