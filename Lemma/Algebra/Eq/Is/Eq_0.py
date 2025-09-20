from util import *


@apply
def apply(self):
    x, y = self.of(Equal)

    return Equal(x - y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a = Symbol(real=True)
    b = Symbol(real=True, zero=False)
    Eq << apply(Equal(a, b))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq_0.of.Eq)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.given.Eq_0)


if __name__ == '__main__':
    run()
# created on 2021-12-29
