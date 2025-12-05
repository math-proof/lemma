from util import *


@apply
def apply(self):
    x = self.of(Sign)
    return Equal(self, -Sign(-x))


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int, Nat

    x, y = Symbol(complex=True)
    Eq << apply(Sign(x - y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1].this.find(Sign).apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Eq[-1].this.find(Equal[0]).apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.find(Equal[0]).apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.find(Equal).reversed

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.rhs.find(Mul).apply(Algebra.Mul.Neg)

    Eq << Eq[-1].this.rhs.find(Abs).apply(Algebra.Abs.Neg)


if __name__ == '__main__':
    run()
# created on 2023-05-25
