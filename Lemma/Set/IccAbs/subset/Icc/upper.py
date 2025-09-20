from util import *


@apply
def apply(self):
    a, b = self.of(Interval)
    return Subset(self.copy(start=abs(a)), self)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, y = Symbol(real=True, given=True)
    Eq << apply(Interval(x, y, left_open=True))

    Eq << Algebra.Le_Abs.apply(x)

    Eq << Set.Subset.Icc.of.Le.upper.apply(Eq[1], y, left_open=True)


if __name__ == '__main__':
    run()
# created on 2019-09-06
