from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(self * a, Sup(fx * a, *limits))


@prove
def prove(Eq):
    from Lemma import Bool, Rat, Real, Nat

    m, M, x, a, b, c = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)))

    Eq << Rat.Lt0Div.of.Gt_0.apply(Eq[0])

    y = Symbol(Eq[1].lhs.args[1])
    Eq << y.this.definition

    Eq <<= Nat.And.of.Eq.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed).reversed

    Eq <<= Real.All.Le.of.LeSup.apply(Eq[-3]), Real.All.Any.Gt.of.GeSup.apply(Eq[-2]), Nat.Eq.given.And.squeeze.apply(Eq[-1])

    y_ = Eq[-3].variable
    Eq <<= Bool.Imp.of.AllSetOf.apply(Eq[-3]), Real.LeSup.given.All.Le.apply(Eq[-2]), Real.GeSup.given.All_Any_Gt.apply(Eq[-1])

    Eq <<= Eq[-3].subs(y_, Eq[2].lhs * y_), Eq[-2].this.expr.apply(Nat.Le.given.And.scale.positive, a, div=True), Bool.All.given.Imp.apply(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-2])

    Eq << Eq[-3].this.rhs.apply(Bool.Any_And.of.Any.All, Eq[0], simplify=None)

    Eq << Eq[-1].this.find(And).apply(Nat.GtMul.of.Gt_0.Gt)

    Eq << Eq[-1].this.lhs.apply(Rat.Lt.given.And.scale.positive, a)

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-20
