from util import *


@apply
def apply(given, M=None):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert b >= a
    if M is None:
        M = given.generate_var(real=True, var='M')
    return Any[M](All[z:domain](f <= M))


@prove
def prove(Eq):
    from Lemma import Real, Algebra, Bool

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Lemma.Real.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << Real.Any.All.Le.of.IsContinuous.extreme_value_theorem.apply(Eq[0])

    Eq << Bool.Any.of.Any.limits.relax.apply(Eq[-1], domain=Reals)

    m = Eq[1].variable
    Eq << Bool.Any.given.Any.subst.apply(Eq[1], m, f(Eq[-1].variable))


if __name__ == '__main__':
    run()
# created on 2020-06-14
