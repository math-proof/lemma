from util import *


@apply
def apply(limited_f, limited_g):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    limited_f = limited_f.of(Equal[0])
    fx, limit = limited_f.of(Limit)
    x, x0 = limit

    gx, S[limit], R = of_limited(limited_g)

    assert R.is_Interval
    return Equal(Limit[x:x0](fx * gx), 0)


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(Limit[x:x0 + S.Infinitesimal](f(x)), 0), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.of.Eq_Limit.limit_definition.apply(Eq[0], ε, δ_0)

    δ_1 = Symbol(real=True, positive=True)
    Eq << Calculus.Any.All.Le.of.IsLimited.boundedness.apply(Eq[1], delta=δ_1, var='B')

    B = Eq[-1].variables[1]
    assert B > 0
    Eq << Eq[-2].subs(ε, ε / B)

    Eq << Algebra.Any.All.And.of.Any_All.Any_All.limits_Inter.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Abs.Mul.of.Lt.Lt)

    Eq << Eq[-1].this.find(Min).apply(Algebra.Min.eq.Add)

    δ = Symbol(real=True, positive=True)
    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], Min(δ_0, δ_1), δ)
    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-10
# updated on 2023-04-16
