from util import *


@apply
def apply(lt, lt_max, x=None):
    U, maxi = lt_max.of(Less)
    _M, _m = maxi.of(Max[Expr ** 2, Expr ** 2])
    if x is None:
        x = lt.generate_var(real=True)
    m, M = lt.of(Less)
    assert {M, m} == {_M, _m}
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat, Int, Int

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m < M, U < Max(M ** 2, m ** 2))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=M > 0)

    Eq <<= Bool.Cond.given.Imp.ImpNot.apply(Eq[-2], cond=m > 0), Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=m > 0)

    Eq <<= Eq[-4].this.apply(Bool.Imp.flatten), Eq[-3].this.apply(Bool.Imp.flatten), Eq[-2].this.apply(Bool.Imp.flatten), Eq[-1].this.apply(Bool.Imp.flatten)

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-4].lhs),\
        Bool.Imp_And.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-3].lhs),\
        Eq[-2].this.lhs.apply(Algebra.Lt.of.Le.Gt),\
        Bool.Imp_And.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq <<= Eq[-3].this.rhs.apply(Bool.And.Imp.And.of.Cond.split, cond=M + m > 0), \
        Eq[-1].this.rhs.args[::2].apply(Algebra.EqMax.of.Le_0.Lt, simplify=None, ret=slice(None)), \
        Eq[-4].this.rhs.args[-1].apply(Nat.Ge.of.Gt), \
        Eq[-2].this.lhs.apply(Nat.Le.of.Lt)

    Eq <<= Bool.And.Imp.of.Imp.apply(Eq[-4], simplify=None), \
        Eq[-3].this.rhs.args[:4:2].apply(Bool.Cond.of.Eq.Cond.subst, simplify=None), \
        Eq[-2].this.rhs.args[::2].apply(Algebra.EqMax.of.Ge_0.Lt, ret=slice(None)), \
        Eq[-1].this.apply(Bool.Imp.Is.ImpNotS)

    Eq <<= Eq[-5].this.rhs.rhs.apply(Bool.Cond.of.And, index=slice(2, None, -2), simplify=None), \
        Eq[-4].this.rhs.rhs.apply(Bool.Cond.of.And, index=slice(3, None, -3), simplify=None), \
        Eq[-3].this.rhs.args[:3].apply(Algebra.Any.GtSquare.of.Le_0.Lt.Lt), \
        Eq[-2].this.rhs.args[::2].apply(Bool.Cond.of.Eq.Cond.subst), \
        Bool.Imp.given.Cond.apply(Eq[-1]).reversed

    Eq <<= Eq[-3].this.rhs.rhs.args[1].apply(Algebra.Gt.transport, lhs=0), \
        Eq[-2].this.rhs.rhs.args[2].apply(Algebra.Le.transport), \
        Eq[-1].this.rhs.apply(Algebra.Any.GtSquare.of.Ge_0.Lt.Lt)

    Eq <<= Eq[-2].this.rhs.rhs.args[1:].apply(Algebra.EqMax.of.Le_0.Gt, ret=1), \
        Eq[-1].this.rhs.rhs.args[1:].apply(Algebra.EqMax.of.Gt_0.Le, ret=0)

    Eq <<= Eq[-2].this.rhs.rhs.args[:2].apply(Bool.Cond.of.Eq.Cond.subst), \
        Eq[-1].this.rhs.rhs.args[:2].apply(Bool.Cond.of.Eq.Cond.subst)

    Eq <<= Eq[-2].this.rhs.apply(Bool.Imp_And.of.ImpAnd), \
        Eq[-1].this.rhs.rhs.args[1].apply(Nat.Ge.of.Gt)

    Eq.is_positive, Eq.is_nonpositive = Eq[-2].this.rhs.rhs.apply(Algebra.Any.GtSquare.of.Le_0.Gt_0.Lt),\
        Eq[-1].this.rhs.apply(Bool.Imp_And.of.ImpAnd)

    Eq <<= Eq.is_nonpositive.this.rhs.rhs.apply(Bool.And.Imp.of.Cond.split, cond=m + M < 0)

    Eq << Eq[-1].this.rhs.apply(Bool.And.Imp.of.Imp)

    Eq << Bool.And.Imp.of.Imp.apply(Eq[-1], simplify=None)

    Eq <<= Eq[-1].this.rhs.rhs.apply(Bool.Cond.of.And, index=slice(None, None, 2)), Eq[-2].this.rhs.rhs.apply(Bool.Cond.of.And, index=0)

    Eq <<= Eq[-2].this.rhs.apply(Bool.Imp_And.of.ImpAnd), Eq[-1].this.rhs.apply(Bool.Imp_And.of.ImpAnd)

    Eq.is_negative = Eq[-2].this.rhs.rhs.apply(Algebra.Any.GtSquare.of.Ge_0.Lt_0.Lt)

    Eq << Eq[-1].this.rhs.rhs.args[0].apply(Int.EqAdd.Is.Eq_Sub, lhs=0)

    Eq << Eq[-1].this.rhs.rhs.apply(Bool.Cond.of.Eq.Cond.subst, ret=0)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp_And.of.Cond.Imp)

    Eq << Eq[-1].this.rhs.rhs.args[1:].apply(Algebra.Any.GtSquare.of.Gt_0.Lt)

    Eq << Eq[-1].this.rhs.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)

    Eq <<= Eq[-1] & Eq.is_negative & Eq.is_positive





if __name__ == '__main__':
    run()
# created on 2019-09-08
# updated on 2023-05-18
