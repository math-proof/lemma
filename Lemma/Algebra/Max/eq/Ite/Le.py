from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, this <= arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Max(x, y))

    Eq << Eq[-1].this.find(LessEqual).reversed
    Eq << Eq[-1].this.lhs.apply(Algebra.Max.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2020-01-25
