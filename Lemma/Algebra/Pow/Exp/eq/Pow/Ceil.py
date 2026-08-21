from util import *


@apply
def apply(self):
    x, m = self.of(Pow[Exp[ImaginaryUnit * Expr], Expr ** -1])
    assert m > 0

    return Equal(self, exp(S.ImaginaryUnit * (x - Ceil(x / (2 * S.Pi) - S.One / 2) * S.Pi * 2) / m))


@prove
def prove(Eq):
    from Lemma import Complex

    x = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(exp(S.ImaginaryUnit * x) ** (1 / n))

    Eq << Complex.ArgExpMulI.eq.Sub_Mul_Ceil.apply(Arg(Eq[0].lhs.base))

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Complex.PowExp_Inv.eq.ExpMulIDivArg)


if __name__ == '__main__':
    run()
# created on 2020-03-02
