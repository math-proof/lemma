from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((x, x > 0), (0, Equal(x, 0)), (-x, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Eq[-1].this.rhs.apply(Logic.Ite.subst, reverse=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Abs.eq.IteGe_0)


if __name__ == '__main__':
    run()
# created on 2018-02-12
