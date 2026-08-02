from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[tanh])
    return Equal(self, sech(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Real, Nat, Nat

    x = Symbol(real=True)
    Eq << apply(Derivative[x](tanh(x)))

    Eq << Eq[0].this.find(tanh).apply(Real.Tanh.eq.Div)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.Div.eq.Div.Sub)

    Eq << Eq[-1].this.find(Derivative).apply(Real.Grad.Sinh.eq.Cosh)

    Eq << Eq[-1].this.find(Derivative).apply(Real.Grad.Cosh.eq.Sinh)

    Eq << Eq[-1].this.lhs.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(sinh).apply(Real.Sinh.eq.Mul.Tanh)

    Eq << Eq[-1].this.rhs.apply(Real.Square.Sech.eq.Sub.Square.Tanh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
