from util import *


@apply
def apply(self):
    x = self.of(Sinh ** 2)
    return Equal(self, cosh(x) ** 2 - 1)


@prove
def prove(Eq):
    from Lemma import Real, Nat

    x = Symbol(real=True)
    Eq << apply(sinh(x) ** 2)

    Eq << Eq[-1].this.find(sinh).apply(Real.Sinh.eq.SubDivSExp_2)

    Eq << Eq[-1].this.lhs.apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)

    Eq << Eq[-1].this.find(cosh).apply(Real.Cosh.eq.AddDivSExp_2)

    Eq << Eq[-1].this.find(Add ** 2).apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)


if __name__ == '__main__':
    run()
# created on 2023-11-26
