from util import *


@apply
def apply(self):
    x, y = self.of(Mul >= 0)
    return Or(And(x >= 0, y >= 0), And(x <= 0, y <= 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y >= 0)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Or.of.Ge_0.split.Mul)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.given.Or.split.Mul)


if __name__ == '__main__':
    run()
# created on 2023-04-18
