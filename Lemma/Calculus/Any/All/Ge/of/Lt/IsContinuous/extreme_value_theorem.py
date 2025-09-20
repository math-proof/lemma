from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    ((f, (z, xi)), _f), (S[xi], domain) = given.of(All[Equal[Limit]])
    assert not xi.infinitesimality
    S[a], S[b] = domain.of(Interval)
    assert domain.is_closed
    assert _f == f._subs(z, xi)
    return Any[xi:domain](All[z:domain](f >= _f))


@prove
def prove(Eq):
    from Lemma import Calculus

    a, b = Symbol(real=True)
    f = Function(real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(a < b, is_continuous(f, a, b))

    # https://en.wikipedia.org/wiki/Bolzano%E2%80%93Weierstrass_theorem
    # https://en.wikipedia.org/wiki/Extreme_value_theorem



if __name__ == '__main__':
    run()
# created on 2023-10-15
# updated on 2023-11-10
