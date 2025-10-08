from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(Sup(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:m:M](f(x)))

    Eq.reciprocal = Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << Algebra.And.of.Eq.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.All.Le.of.LeSup.apply(Eq[-2]), Algebra.All.Any.Gt.of.GeSup.apply(Eq[-1], z)

    Eq <<= Bool.Imp.of.AllSetOf.apply(Eq[-2]), Bool.Imp.of.AllSetOf.apply(Eq[-1])

    Eq <<= Bool.Imp_And.of.Cond.Imp.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.LeMul.of.Gt_0.Le), Bool.ImpAndS.of.Imp.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.GtMul.of.Gt_0.Gt)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.given.And.scale.positive, a)

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeSup.given.All.Le.apply(Eq[-2]), Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1], z)

    Eq <<= Bool.All.given.Imp.apply(Eq[-2]), Bool.All.given.Imp.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-08-21
# updated on 2023-05-14
