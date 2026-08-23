from util import *


@apply
def apply(eq, interval, x=None):
    fx, f_x = eq.of(Equal)
    assert f_x._subs(x, -x) == -fx

    return Equal(Sup[x:-interval](fx), -Inf[x:interval](fx))


@prove
def prove(Eq):
    from Lemma import Algebra, Real, Bool, Nat

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(f(x), -f(-x)), Interval(m, M, right_open=True), x)

    y = Symbol(-Eq[1].rhs)
    Eq << y.this.definition

    Eq <<= Nat.And.of.Eq.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed)

    z = Symbol(real=True)
    Eq <<= Real.All.Any.Lt.of.LeInf.apply(Eq[-3], z), Real.All.Ge.of.GeInf.apply(Eq[-2]), Nat.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Eq[-4].this.expr.apply(Bool.Any.of.Any.limits.Neg), Bool.All.of.All.limits.subst.Neg.real.apply(Eq[-3], x, -x), \
        Real.LeSup.given.All.Le.apply(Eq[-2]), Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1], z)

    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0])

    Eq <<= -Eq[-2].this.expr, -Eq[-1].this.expr.expr
    Eq << Eq[-1].this.apply(Bool.All.limits.subst.Neg.real, z, -z)


if __name__ == '__main__':
    run()
# created on 2019-04-12
