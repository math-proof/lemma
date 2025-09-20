from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Inf)
    return Equal(Inf(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Inf[x:m:M](f(x)))

    Eq.reciprocal = Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << Algebra.And.of.Eq.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.All.Any.Lt.of.LeInf.apply(Eq[-2], z), Algebra.All.Ge.of.GeInf.apply(Eq[-1])

    Eq <<= Logic.Imp.of.AllSetOf.apply(Eq[-2]), Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq <<= Eq[-2].subs(z, z * Eq.reciprocal.lhs), Logic.Imp_And.of.Cond.Imp.apply(Eq[0], Eq[-1])

    Eq <<= Logic.ImpAndS.of.Imp.apply(Eq[-2], cond=Eq[0]), Eq[-1].this.rhs.apply(Algebra.GeMul.of.Gt_0.Ge)

    Eq << Eq[-2].this.rhs.apply(Logic.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.LtMul.of.Gt_0.Lt)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Gt.given.And.scale.positive, a)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], z), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq <<= Logic.All.given.Imp.apply(Eq[-2]), Logic.All.given.Imp.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-13
