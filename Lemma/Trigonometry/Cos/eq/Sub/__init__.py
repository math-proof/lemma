from util import *


@apply
def apply(self, index=-1):
    x, y = std.array_split(self.of(cos[Add]), index)
    x, y = Add(*x), Add(*y)
    return Equal(self, cos(x) * cos(y) - sin(x) * sin(y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x + y))













    Eq << Trigonometry.Cosh.eq.Add.apply(cosh(x + y))

    Eq << Eq[-1].subs(x, x * S.ImaginaryUnit).subs(y, y * S.ImaginaryUnit)





if __name__ == '__main__':
    run()

# created on 2018-06-15
# updated on 2023-11-26

from . import Square
from . import double
