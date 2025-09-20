from util import *


@apply
def apply(self):
    eqs = self.of(Bool[And])
    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y, a, b = Symbol(real=True)
    Eq << apply(Bool((x > y) & (a > b)))

    Eq << Eq[0].this.rhs.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite, index=0)

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2018-02-14
