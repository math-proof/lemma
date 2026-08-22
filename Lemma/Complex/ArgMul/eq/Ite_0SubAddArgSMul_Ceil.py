from util import *


@apply
def apply(self):
    args = self.of(Arg[Mul])
    s = Add(*(Arg(arg) for arg in args))
    return Equal(self, Piecewise((0, Or(*(Equal(arg, 0) for arg in args))), (s - Ceil(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi, True)))


@prove
def prove(Eq):
    from Lemma import Bool, Nat, Complex

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Arg(x * y))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Eq[0].find(Or))

    Eq << Bool.Imp_Ite.given.Imp.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Nat.MulSubS.eq.Zero.of.OrEqS)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Bool.Imp_Ite.given.Imp.apply(Eq[2], invert=True)

    Eq << Eq[-1].this.lhs.apply(Complex.ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0)


if __name__ == '__main__':
    run()

# created on 2018-10-26
