from util import *


@apply
def apply(self):
    x, y = self.of(LessEqual)
    return LessEqual(x - y, Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le_0.of.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.given.Le_0)


if __name__ == '__main__':
    run()
# created on 2023-04-18
