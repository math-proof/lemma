from util import *


@apply
def apply(is_limited):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, positive=True)
    return Equal(Limit[x:x0](log(fx)), log(Limit[x:x0](fx)))


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus, Set, Algebra, Logic

    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Interval.open(0, oo)))

    epsilon0, delta0, delta, epsilon = Symbol(positive=True)
    Eq << Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq << Eq[0].subs(Eq.is_limited)

    Eq.A_is_positive = Set.Gt_0.of.IsPositive.apply(Eq[-1])

    Eq << Algebra.EqLog.of.Gt_0.Eq.apply(Eq.A_is_positive, Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Set.Ne_0.of.In.apply(Eq[0])

    Eq << Eq[-2].this.apply(Calculus.Eq.Is.Any_All.limit_definition, delta=delta, epsilon=epsilon)

    Eq << Eq[-1].this.expr.expr.lhs.arg.apply(Algebra.Add.eq.Log)

    Eq << Eq[2].this.expr.expr.apply(Algebra.And.of.Lt.split.Abs)

    Eq << Eq[-1].this.expr.expr.args[0].apply(Algebra.Lt.transport, lhs=0)

    Eq << Eq[-1].this.expr.expr.args[0].apply(Algebra.Gt.transport, lhs=0)

    Eq << Eq[-1].this.expr.expr.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Algebra.Any.All.And.of.Cond.Any_All.apply(Eq.A_is_positive, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Set.In.Div.of.Gt_0.In)

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.expr.expr.rhs.args[1].apply(Algebra.Mul_Add.eq.AddMulS)

    epsilon1 = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    Eq << Algebra.Or.of.Cond.subst.apply(Eq[-1], epsilon0, epsilon1 * A)

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq.A_is_positive * epsilon1, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-19
