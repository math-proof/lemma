from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    y0 = a * m + b
    y1 = a * M + b

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x + b, x)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=a > 0)

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=a < 0)

    Eq <<= Eq[-3].this.lhs.apply(Algebra.Sup.eq.MaxAddS_Mul.of.Gt_0.Lt, a * x + b, x), Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Sup.eq.MaxAddS_Mul.of.Lt_0.Lt, a * x + b, x), Logic.Imp.given.Cond.apply(Eq[-1])

    Eq <<= Eq[-1].this.find(Sup).simplify()

    Eq <<= Set.Icc.ne.Empty.of.Lt.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-12-25

