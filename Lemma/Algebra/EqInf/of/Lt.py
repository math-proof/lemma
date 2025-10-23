from util import *


@apply
def apply(lt, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x), m)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Nat

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x)

    Eq.eq_max = Nat.EqMax.of.Lt.apply(Eq[0])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    y = Symbol(real=True)
    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], y), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.given.And.All.split.apply(Eq[-2], cond=y <= M), Bool.All.given.All_Or_Not.apply(Eq[-1])

    Eq <<= Eq[-2].subs(Eq.eq_max), Eq[-3].this.expr.apply(Algebra.Any.given.Cond.subst, x, (m + y) / 2), Eq[-1].this.find(NotElement).apply(Set.NotIn_Icc.given.OrLtS)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.given.Cond.subst, x, (m + M) / 2), Bool.All_And.given.All.All.apply(Eq[-1])

    Eq <<= Bool.And_And.given.And.Cond.apply(Eq[-3]), Bool.All.given.Imp.apply(Eq[-2]), Bool.All.given.Imp.apply(Eq[-1])

    Eq << Set.In.Icc.of.Lt.average.apply(Eq[0])

    Eq <<= Bool.All.given.Imp.apply(Eq[-3]), Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(Set.In.given.In.Mul.Icc, 2)

    Eq <<= Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-3]), Eq[-2].this.rhs - y, Eq[-1].this.rhs.apply(Set.In.given.In.Sub, m)

    Eq << Eq[-2].this.lhs.apply(Set.Gt.of.In_Icc)

    Eq <<= Eq[-3].this.lhs.apply(Algebra.Gt.of.Lt.Gt, ret=1), Eq[-1].this.rhs.apply(Set.In.given.And.strengthen, lower=M, strict=True)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.GtAdd.of.Gt.Gt), Bool.Imp.given.Cond.apply(Eq[-1])

    Eq << Eq[-1] + (m - M)

    Eq << Eq[-2].this.rhs * 2





if __name__ == '__main__':
    run()
# created on 2019-08-27
# updated on 2023-05-12
