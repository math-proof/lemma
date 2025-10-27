from util import *


@apply
def apply(self):
    eqs = self.of(Bool[And])
    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat
    x, y, a, b = Symbol(real=True)
    Eq << apply(((x > y) & (a > b)).toNat)

    Eq << Eq[0].this.rhs.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite, index=0)

    Eq << Eq[-1].this.lhs.apply(Bool.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2018-02-14
