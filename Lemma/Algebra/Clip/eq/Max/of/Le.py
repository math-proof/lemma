from util import *


@apply
def apply(le, x):
    a, b = le.of(LessEqual)
    return Equal(clip(x, a, b), Max(Min(x, b), a))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, a, b = Symbol(real=True)
    Eq << apply(a <= b, x)

    Eq << Nat.EqMin.of.Le.apply(Eq[0])

    Eq << Eq[0].reversed

    Eq << Eq[1].this.find(clip).defun()

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=a <= x)

    Eq <<= Eq[-2].this.find(Min[~Max]).apply(Algebra.Max.eq.Ite.Lt), Eq[-1].this.find(Min[~Max]).apply(Algebra.Max.eq.Ite.Lt)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.lhs.reversed

    Eq <<= Bool.Imp.given.Imp.subst.Bool.apply(Eq[-2], invert=True), Bool.Imp.given.Imp.subst.Bool.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq_Max.given.Ge), Eq[-1].subs(Eq[2])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.GeMin.given.And.Ge), Eq[-1].this.rhs.apply(Algebra.Eq_Max.given.Ge)

    Eq << Bool.Imp.given.Cond.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Nat.EqMin.of.Lt)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-26
