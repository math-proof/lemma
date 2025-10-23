from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((-x, x < 0), (x, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Int.Abs.eq.IteGe_0.apply(abs(x))

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)


if __name__ == '__main__':
    run()
# created on 2018-02-13
