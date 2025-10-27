from util import *


@apply
def apply(self):
    arg, *args = self.of(Min)
    this = self.func(*args)
    rhs = Piecewise((arg, arg < this), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[-1].this.find(Less).reversed

    Eq << Eq[-1].this.lhs.apply(Nat.Min.eq.IteGt)


if __name__ == '__main__':
    run()
# created on 2018-08-31
