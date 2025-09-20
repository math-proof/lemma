from util import *


@apply
def apply(given, m=None):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    assert not xi.infinitesimality
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert b >= a
    if m is None:
        m = given.generate_var(real=True, var='m')
    return Any[m](All[z:domain](f >= m))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << Calculus.Any.All.Ge.of.IsContinuous.extreme_value_theorem.apply(Eq[0])

    Eq << Algebra.Any.of.Any.limits.relax.apply(Eq[-1], domain=Reals)
    m = Eq[1].variable
    Eq << Algebra.Any.given.Any.subst.apply(Eq[1], m, f(Eq[-1].variable))



if __name__ == '__main__':
    run()
# created on 2020-06-13
