from util import *


@apply
def apply(is_limited):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, positive=True)
    return Element(Limit[x:x0](log(fx)), Reals)


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus, Set, Algebra

    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Interval.open(0, oo)))

    epsilon, epsilon0, delta0 = Symbol(positive=True)
    Eq << Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq << Eq[0].subs(Eq.is_limited)

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[-1])

    Eq << Algebra.EqLog.of.Gt_0.Eq.apply(Eq[-1], Eq.is_limited)


if __name__ == '__main__':
    run()
# created on 2020-06-20
