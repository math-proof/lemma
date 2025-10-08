from util import *


@apply
def apply(limited_f, limited_g):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, real=True)
    gx, S[(x, x0)] = of_limited(limited_g, nonzero=True)

    assert not x0.infinitesimality
    return Equal(Limit[x:x0](fx / gx), limited_f.lhs / limited_g.lhs)


@prove
def prove(Eq):
    from Lemma import Calculus, Set, Algebra, Bool

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Reals), Element(Limit[x:x0](g(x)), Reals - {0}))

    Eq.inverse = Calculus.EqInv.of.IsLimited.algebraic_limit_theorem.apply(Eq[1])

    Eq << Set.IsReal.Inv.of.In.apply(Eq[1])

    Eq << Bool.Cond.of.Eq.Cond.subst.apply(Eq.inverse, Eq[-1], reverse=True)

    Eq << Calculus.EqMul.of.IsLimited.IsLimited.algebraic_limit_theorem.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].subs(Eq.inverse)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-06-22
