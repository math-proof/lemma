from util import *


@apply
def apply(eq_limit):
    tangent, (epsilon, S[-S.Infinitesimal]) = eq_limit.of(Equal[Limit, Infinity])
    delta = tangent * epsilon
    fx1, fx = delta.of(Expr - Expr)
    for x in fx.free_symbols:
        if fx1 == fx._subs(x, x + epsilon):
            break
    else:
        raise

    return Limit[epsilon:-S.Infinitesimal](fx1) < fx


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus, Algebra, Set

    x, epsilon = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[epsilon:-S.Infinitesimal]((f(x + epsilon) - f(x)) / epsilon), oo))

    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[0], 'chi')

    Eq << Eq[-1].this.expr.apply(Algebra.All.And.of.All)

    Eq << Eq[-1].this.find(Element).apply(Set.Lt.of.In_Icc)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.LtMul.of.Lt_0.Gt)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.transport, lhs=0)


if __name__ == '__main__':
    run()
# created on 2020-04-27
