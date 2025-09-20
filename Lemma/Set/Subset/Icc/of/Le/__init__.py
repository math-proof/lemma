from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, a), Interval(a, b))


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Set.EqIcc.of.Le.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Set.InterSingletonS.subset.Icc.apply(x, y)


if __name__ == '__main__':
    run()
# created on 2020-06-03
from . import lower
from . import upper
del Ge
from . import Ge
