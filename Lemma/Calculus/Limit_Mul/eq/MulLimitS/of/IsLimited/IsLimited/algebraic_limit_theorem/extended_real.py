from util import *


@apply
def apply(limited_f, limited_g):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, extended_real=True)

    gx, S[(x, x0)] = of_limited(limited_g, extended_real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove(proved=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), ExtendedReals), Element(Limit[x:x0 + S.Infinitesimal](g(x)), ExtendedReals - {0}))

    Eq << Reals - {0}

    Eq << ExtendedReals - {0}


if __name__ == '__main__':
    run()
# created on 2021-08-14
