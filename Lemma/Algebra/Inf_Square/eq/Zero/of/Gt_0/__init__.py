from util import *


@apply
def apply(is_positive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    if x is None:
        x = M.generate_var(real=True)

    self = Inf[x:Interval(0, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, x=x)

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[0])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[1])

    t = Symbol(real=True)
    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], t), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq << Algebra.All.given.And.All.split.apply(Eq[-1], cond=t <= M ** 2)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Any.given.Cond.subst, x, sqrt(t) / 2)

    Eq <<= Eq[-1].this.find(Less).apply(Algebra.Lt.given.Gt_0), Eq[-2].this.expr.apply(Algebra.Any.given.Cond.subst, x, M / 2)

    Eq <<= Eq[-2].this.find(Greater) * Rational(4, 3), Eq[-1].this.args[0].apply(Set.In_Ico.given.Ge.Lt)

    Eq <<= Logic.All_And.given.All.All.apply(Eq[-2]), Eq[-1].this.args[0].apply(Algebra.Lt.given.Gt_0)

    Eq <<= Logic.All.given.All_Or_Not.apply(Eq[-3]), Eq[-2].this.expr.apply(Set.In_Ico.given.Ge.Lt), Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= Eq[-4].this.args[1].apply(Set.NotIn_Icc.given.OrLtS)

    Eq <<= Logic.All.given.Imp.apply(Eq[-3]), Eq[-2] * 2, Logic.All.given.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-1].this.rhs * 4

    Eq <<= Eq[-2].this.lhs.apply(Algebra.LeSqrt.of.Gt_0.Le, ret=0), Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].subs(Eq[2]), Eq[-1].this.lhs.apply(Algebra.Gt.of.Gt.relax, lower=0, ret=0)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Gt_0.Sqrt.of.Gt_0), Eq[-1].this.lhs.args[0].apply(Algebra.Gt.of.Gt_0.scale, 4)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Gt.of.Gt.Gt)

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-2])

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Lt.of.Gt_0.scale, S.One / 2), Logic.Imp_And.given.Imp.delete.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Lt.of.Le.Lt)

    Eq <<= Eq[-1].this.lhs / 2


if __name__ == '__main__':
    run()
# created on 2019-08-15

from . import Lt_0
from . import Le_0
