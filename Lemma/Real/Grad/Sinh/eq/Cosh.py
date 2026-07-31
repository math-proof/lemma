from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[sinh])
    return Equal(self, cosh(x))


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(Derivative[x](sinh(x)))

    Eq << Eq[0].this.find(sinh).apply(Real.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.rhs.apply(Real.Cosh.eq.AddDivSExp_2)


if __name__ == '__main__':
    run()
# created on 2023-11-26
