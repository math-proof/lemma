from util import *


@apply
def apply(limited_f, limited_g):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, positive=True)
    gx, S[(x, x0)] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx ** gx), limited_f.lhs ** limited_g.lhs)


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus, Algebra, Set

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Interval.open(0, oo)), Element(Limit[x:x0](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    Eq << Eq[-1].subs(ε_0, ε / 2)

    ε_1 = Symbol(real=True, positive=True)
    δ_1 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[1], ε_1, δ_1, var='B')

    Eq << Eq[-1].subs(ε_1, ε / 2)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Abs.Add.of.Lt.Lt)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Set.Lt.given.In.Icc)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(Set.Lt.given.In.Icc)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    δ = Symbol(real=True, positive=True)
    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-06-22
