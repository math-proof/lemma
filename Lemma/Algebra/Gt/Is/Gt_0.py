from util import *


@apply
def apply(self):
    x, y = self.of(Greater)
    return Greater(x - y, Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.of.Gt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.given.Gt_0)




if __name__ == '__main__':
    run()
# created on 2023-04-18
