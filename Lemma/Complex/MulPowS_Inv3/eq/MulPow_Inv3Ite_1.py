from util import *


@apply
def apply(self):
    A, B = self.of(Mul)
    A = A.of(Expr ** (S.One / 3))
    B = B.of(Expr ** (S.One / 3))
    C = (A * B) ** (S.One / 3)
    d = Ceil((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    return Equal(self, C * Piecewise((1, Equal(A, 0) | Equal(B, 0) | Equal(d, 0)), (w, Arg(A) + Arg(B) > S.Pi), (~w, True)))


@prove
def prove(Eq):
    from Lemma import Bool, Complex

    A, B = Symbol(complex=True, given=True)
    Eq << apply(A ** (S.One / 3) * B ** (S.One / 3) )

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(A, 0) | Equal(B, 0))

    Eq << Bool.Imp_Ite.given.Imp.apply(Eq[-2])

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-2])

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Bool.Imp_Ite.given.Imp.apply(Eq[2], invert=True)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Eq[-1].find(ExprCondPair[~Equal]))

    Eq <<= Bool.Imp.given.ImpEq.apply(Eq[-2]), Bool.Imp_Ite.given.Imp.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(Bool.Imp_Imp.Is.ImpAnd), Eq[-1].this.lhs.apply(Complex.OrEqSCeil.of.CeilSubDivAddArgS.ne.Zero)

    Eq << Eq[-2].this.lhs.apply(Complex.MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS)

    Eq << Eq[-1].this.find(Greater).apply(Complex.GtAddArgS.Is.EqCeilSubDivS, simplify=None)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Bool.Imp.given.ImpEq.apply(Eq[-2]), Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Bool.Imp_Imp.Is.ImpAnd), Eq[-1].this.apply(Bool.Imp_Imp.Is.ImpAnd)
    Eq <<= Eq[-2].this.lhs.apply(Complex.MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS)
    Eq <<= Eq[-1].this.lhs.apply(Complex.MulPowS_Inv3.eq.MulPow_Inv3.of.EqCeilSubDivAddArgS)
    Eq << Eq[-1].this.find(Add ** -1).apply(Complex.Expr.eq.AddRe_MulIIm)


if __name__ == '__main__':
    run()
# created on 2018-11-01
