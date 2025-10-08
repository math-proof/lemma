from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(self * a, Sup(fx * a, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    m, M, x, a, b, c = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)))

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    y = Symbol(Eq[1].lhs.args[1])
    Eq << y.this.definition

    Eq <<= Algebra.And.of.Eq.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed).reversed

    Eq <<= Algebra.All.Le.of.LeSup.apply(Eq[-3]), Algebra.All.Any.Gt.of.GeSup.apply(Eq[-2]), Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    y_ = Eq[-3].variable
    Eq <<= Bool.Imp.of.AllSetOf.apply(Eq[-3]), Algebra.LeSup.given.All.Le.apply(Eq[-2]), Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1])

    Eq <<= Eq[-3].subs(y_, Eq[2].lhs * y_), Eq[-2].this.expr.apply(Algebra.Le.given.And.scale.positive, a, div=True), Bool.All.given.Imp.apply(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-2])

    Eq << Eq[-3].this.rhs.apply(Bool.Any_And.of.Any.All, Eq[0], simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.GtMul.of.Gt_0.Gt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt.given.And.scale.positive, a)

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-20
