from util import *


@apply
def apply(self):
    x = self.of(Tanh)

    return Equal(self, (Exp(x) - Exp(-x)) / (Exp(x) + Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Real, Rat

    x = Symbol(real=True)
    Eq << apply(tanh(x))

    Eq << Eq[0].this.lhs.apply(Real.Tanh.eq.Div)

    Eq << Eq[-1].this.find(sinh).apply(Real.Sinh.eq.SubDivSExp_2)

    Eq << Eq[-1].this.find(cosh).apply(Real.Cosh.eq.AddDivSExp_2)

    Eq << Eq[-1].this.lhs.apply(Rat.Div.cancel, 2)




if __name__ == '__main__':
    run()
# created on 2023-11-26
