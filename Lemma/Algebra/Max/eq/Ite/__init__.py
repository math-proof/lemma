from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, arg >= this), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True)
    Eq << apply(Max(x, y))


if __name__ == '__main__':
    run()



# created on 2018-08-06
del Le
del Lt
del Gt
from . import Lt
from . import Gt
from . import Le
