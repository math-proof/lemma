from util import *


@apply
def apply(given):
    ((f, (z, xi)), _f), (S[xi], domain) = given.of(All[Equal[Limit]])
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert _f == f._subs(z, xi)
    assert a <= b
    return Any[xi:domain](All[z:domain](f <= _f))


@prove
def prove(Eq):
    from Lemma import Calculus

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << Less(a, b, plausible=True)

    Eq << Calculus.Any.All.Le.of.Lt.IsContinuous.extreme_value_theorem.apply(Eq[-1], Eq[0])



if __name__ == '__main__':
    run()
# created on 2020-06-14
# updated on 2023-10-15
