from util import *


@apply
def apply(M_is_positive, lt, x=None):
    M = M_is_positive.of(Expr > 0)
    U, m2 = lt.of(Less)
    S[M] = m2.of(Expr ** 2)

    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(-M, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    M, U = Symbol(real=True, given=True)
    Eq << apply(M > 0, U < M ** 2)

    x = Eq[-1].variable
    Eq.is_negative, Eq.is_nonnegative = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=U < 0)

    Eq << Bool.Imp.of.Cond.apply(Eq[0], cond=U >= 0)

    Eq << Bool.Imp_And.of.Cond.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtSqrt.of.Ge_0.Lt)

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq.is_negative.this.rhs.apply(Algebra.Any.given.Cond.subst, x, 0)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.In_Ico.given.Ge.Lt)

    Eq << Bool.Imp.given.Cond.apply(Eq[-1])

    Eq << Eq[0].reversed

    Eq << Eq.is_nonnegative.this.rhs.apply(Algebra.Any.given.Cond.subst, x, (sqrt(U) + M) / 2)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt.given.Gt_0), Eq[-1].this.rhs.apply(Set.In_Ico.given.Ge.Lt)

    Eq <<= Eq[-2].this.find(Add).apply(Algebra.Sub.Square.eq.Mul), Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Mul.gt.Zero.given.And.Gt_0), Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Bool.Imp_And.given.Imp.Imp.apply(Eq[-3]), Eq[-2].this.rhs.apply(Algebra.Lt.transport, lhs=0), Eq[-1].this.rhs.apply(Algebra.Gt.given.Gt_0)

    Eq <<= Eq[-3].this.rhs * 2, Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(Algebra.Add.gt.Zero.given.And, index=1)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Add.gt.Zero.given.And, index=0), Eq[-2].this.rhs.apply(Algebra.Gt.transport), Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Bool.Imp_And.given.Imp.Imp.apply(Eq[-4]), Eq[-3].this.rhs.reversed, Eq[-2].this.rhs / 3, Eq[-1].this.lhs.apply(Algebra.GeSqrt_0.of.Ge_0)

    Eq << Eq[-1].this.rhs / 3





if __name__ == '__main__':
    run()
# created on 2019-08-26
# updated on 2023-05-20
