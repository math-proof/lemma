from util import *


@apply
def apply(self):
    x, y = self.of(Arg[Expr + ImaginaryUnit * Expr])
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(x, 0) & Equal(y, 0)),
                                 (asin(y / r), x >= 0),
                                 (S.Pi - asin(y / r), y >= 0),
                                 (-S.Pi - asin(y / r), True)))


@prove
def prove(Eq):
    from Lemma import Bool, Int, Nat, Real, Rat, Complex

    x, y = Symbol(real=True)
    Eq << apply(Arg(x + y * S.ImaginaryUnit))

    Eq << Eq[0].this.lhs.apply(Complex.ArgAdd.eq.Ite_0Ite_Arccos_NegArccos)

    Eq << Eq[-1].this.find(acos).apply(Real.Arccos.eq.Ite_Arcsin_Sub_Arcsin)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite_Ite.eq.Ite__Ite, 1)

    Eq << Eq[-1].this.find(acos).apply(Real.Arccos.eq.Ite_Arcsin_Sub_Arcsin)

    Eq << Eq[-1].this.find(-Piecewise).apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq.eq = Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not)

    ou = Eq.eq.find(Or)
    Eq.equivalent = Iff(ou & (x / sqrt(x ** 2 + y ** 2) >= 0), (x >= 0) & ou, plausible=True)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq <<= Eq[-2].this.find(Or).apply(Real.GtSqrt_0.of.OrNeS_0), Eq[-1].this.find(Or).apply(Real.GtSqrt_0.of.OrNeS_0)

    Eq <<= Eq[-2].this.lhs.apply(Int.Le0Mul.of.Ge_0.Gt_0), Eq[-1].this.lhs.apply(Rat.GeDivS.of.Ge.Gt_0)

    Eq << Bool.UFnIte.given.UFnIte.Iff.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__IteAndNot.eq.Ite__Ite)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 1)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 0, 3)

    Eq << Bool.UFnIte.given.UFnIte.Iff.apply(Eq[-1], old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)

    Eq.eq1 = Eq[-1].this.lhs.apply(Bool.Ite__IteAndNot.eq.Ite__Ite, 0, 3)

    Eq.suffice = Imply(y >= 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    Eq << Eq[-1].this.lhs.apply(Int.EqAbs.of.Ge_0)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq.eq2 = Bool.Ite.of.Imp_Eq.apply(Eq.suffice, Eq.eq1.lhs)

    Eq.suffice = Imply(y < 0, Equal(asin(sqrt(1 - x ** 2 / (x ** 2 + y ** 2))), -asin(y / sqrt(x ** 2 + y ** 2))), plausible=True)

    Eq << Eq.suffice.this.find(Pow).base.apply(Rat.SubDivS1.eq.DivSub.of.Ne_0.Ne_0)

    Eq << Eq[-1].this.lhs.apply(Int.Abs.eq.Neg.of.Lt_0)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Bool.Ite__Ite.eq.Ite__IteAnd_Not.apply(Eq.eq2.rhs, 1, 2)

    Eq << Bool.Ite.of.Imp_Eq.apply(Eq.suffice, Eq[-1].rhs)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.eq2, Eq[-1])

    Eq << Eq.eq1.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 1, 2)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 2, 1)

    Eq << Bool.Ite.of.Imp_Eq.apply(Eq.suffice, Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 2)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 2)





if __name__ == '__main__':
    run()
# created on 2018-07-24
# updated on 2023-05-10
