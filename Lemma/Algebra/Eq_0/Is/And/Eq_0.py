from util import *


@apply
def apply(self):
    z = self.of(Equal[0])
    x = Re(z)
    y = Im(z)
    return Equal(x, 0) & Equal(y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    z = Symbol(complex=True, given=True)
    Eq << apply(Equal(z, 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.lhs.apply(Algebra.Expr.eq.AddRe_MulIIm)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAbs.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqPowS.of.Eq, exp=2)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.Eq_0.of.Add.eq.Zero)

    Eq << Eq[2].this.rhs.lhs.apply(Algebra.Expr.eq.AddRe_MulIIm)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()
# created on 2018-06-11
# updated on 2023-05-20
