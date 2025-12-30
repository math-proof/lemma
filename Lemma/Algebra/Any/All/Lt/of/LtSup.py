from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Sup < Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval.open(-oo, M0)](All(fx < M, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Nat, Nat

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(a, b, left_open=True, right_open=True)](f(x)) < M0, M)

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition

    Eq <<= Algebra.All.Le.of.Eq_Sup.apply(Eq[-1]), Eq[0].subs(Eq[-1].reversed), Algebra.Any.given.Cond.subst.apply(Eq[1], M, (y + M0) / 2)

    Eq.all, *Eq[-2:] = Algebra.All.And.of.Cond.All.apply(Eq[-2], Eq[-3], simplify=None), Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Set.In.given.In.Mul.Icc.apply(Eq[-2], 2)

    Eq << Set.In.given.In.Sub.apply(Eq[-1], M0)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Algebra.All_GeSup.apply(Eq[-1].lhs)

    Eq << Algebra.Cond.of.All.subst.apply(Eq[-1], x, (a + b) / 2)

    Eq << Nat.Gt_Sub_1.of.Ge.apply(Eq[-1], -oo)

    Eq << Eq.all.this.expr.apply(Algebra.Lt.of.Lt.Le, ret=1)

    Eq << Eq[-1].this.expr.apply(Algebra.LtAdd.of.Lt.Le)

    Eq << Eq[-1].this.expr / 2





if __name__ == '__main__':
    run()
# created on 2018-12-28
# updated on 2023-05-20
