from util import *


@apply
def apply(is_nonzero, eq, delta=None):
    A = is_nonzero.of(Unequal[0])
    assert A.is_real
    fx, (x, x0) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    x0, dir = x0.clear_infinitesimal()
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Bool

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Unequal(A, 0), Equal(Limit[x:x0](f(x)), A))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[2], cond=A > 0)

    Eq.gt, Eq.le = Bool.And.Imp.of.Cond.split.apply(Eq[1], cond=A > 0)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq.gt)

    Eq << Eq[-1].this.rhs.apply(Calculus.Any.All.Gt.of.Gt_0.Eq_Limit)

    Eq << (A > 0).this.apply(Algebra.EqAbs.of.Gt_0)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Gt_0.of.Gt.trans, ret=0)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].apply(Algebra.EqAbs.of.Gt_0)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)

    Eq << And(A <= 0, Eq[0]).this.apply(Algebra.Lt_0.of.Ne_0.Le_0)

    Eq << Eq[-1].this.apply(Bool.Imp.fold)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq <<= Eq.le & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Calculus.Any.All.Lt.of.Lt_0.Eq_Limit)

    Eq << (A <= 0).this.apply(Algebra.EqAbs.of.Le_0)

    Eq << -Eq[-1].this.rhs

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Lt_0.of.Lt.trans, ret=0)

    Eq << Eq[-1].this.find(Expr < 0).apply(Algebra.EqAbs.of.Lt_0)

    Eq << -Eq[-1].this.find(Equal)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)

    Eq << -Eq[-1].this.rhs.expr.expr





if __name__ == '__main__':
    run()
# created on 2020-05-15
# updated on 2023-05-12
