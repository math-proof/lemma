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
    from Lemma import Real, Algebra, Bool

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Lemma.Real.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << Real.Any.All.Ge.of.IsContinuous.extreme_value_theorem.apply(Eq[0])

    Eq << Bool.Any.of.Any.limits.relax.apply(Eq[-1], domain=Reals)
    m = Eq[1].variable
    Eq << Bool.Any.given.Any.subst.apply(Eq[1], m, f(Eq[-1].variable))



if __name__ == '__main__':
    run()
# created on 2020-06-13
