from util import *


@apply
def apply(is_negative, self, div=False):
    a = is_negative.of(Expr < 0)
    fx, *limits = self.of(Inf)
    if div:
        return Equal(self, Sup(fx * a, *limits) / a)
    return Equal(self, a * Sup(fx / a, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < 0, Inf[x:m:M](f(x) * a))

    Eq.reciprocal = Algebra.Div.lt.Zero.of.Lt_0.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << Algebra.And.of.Eq.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.All.Le.of.LeSup.apply(Eq[-2]), Algebra.All.Any.Gt.of.GeSup.apply(Eq[-1], z)

    Eq <<= Logic.Imp.of.AllSetOf.apply(Eq[-2]), Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq <<= Logic.Imp_And.of.Cond.Imp.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.GeMul.of.Lt_0.Le), Logic.ImpAndS.of.Imp.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(Logic.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.LtMul.of.Lt_0.Gt)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Lt.given.And.scale.negative, a)

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], z), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq <<= Logic.All.given.Imp.apply(Eq[-2]), Logic.All.given.Imp.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-12-22
# updated on 2021-10-02
