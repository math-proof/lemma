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
    from Lemma import Algebra, Bool

    A, B = Symbol(complex=True, given=True)
    Eq << apply(A ** (S.One / 3) * B ** (S.One / 3) )

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(A, 0) | Equal(B, 0))

    Eq << Bool.Imp.given.Imp.subst.Bool.apply(Eq[-2])

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-2])

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Bool.Imp.given.Imp.subst.Bool.apply(Eq[2], invert=True)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Eq[-1].find(ExprCondPair[~Equal]))

    Eq <<= Bool.Imp.given.ImpEq.apply(Eq[-2]), Bool.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(Bool.Imp.flatten), Eq[-1].this.lhs.apply(Algebra.Or_Eq.Arg.of.Ceil.ne.Zero)

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq.of.Ne_0.Ne_0.Eq.cubic_root)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Gt_Arg.Is.Eq_Ceil, simplify=None)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Bool.Imp.given.ImpEq.apply(Eq[-2]), Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Bool.Imp.flatten), Eq[-1].this.apply(Bool.Imp.flatten)
    Eq <<= Eq[-2].this.lhs.apply(Algebra.Eq.of.Ne_0.Ne_0.Eq.cubic_root)
    Eq <<= Eq[-1].this.lhs.apply(Algebra.Eq.of.Ne_0.Ne_0.Eq.cubic_root)


if __name__ == '__main__':
    run()
# created on 2018-11-01
