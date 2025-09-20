from util import *


@apply
def apply(given, ε=None, δ=None, var=None):
    from Lemma.Calculus.Any.All.of.IsLimited.limit_definition import of_limited
    from Lemma.Calculus.Eq.Is.Any_All.limit_definition import Any_All
    fn, (x, x0), *R = of_limited(given)

    A = fn.generate_var(excludes={x}, **fn.type.dict)

    cond = Any_All(Equal(given.lhs, A), ε, δ)
    B = fn.generate_var(excludes={x}, definition=given.lhs, var=var)
    return cond._subs(A, B)


@prove
def prove(Eq):
    from Lemma import Calculus

    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    Eq << apply(Element(Limit[x:oo](f(x)), Reals), var='A')

    Eq << Calculus.Any.All.of.IsLimited.limit_definition.apply(Eq[0])

    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-04-08
