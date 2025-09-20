from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    ((f, (z, xi)), _f), (S[xi], domain) = given.of(All[Equal[Limit]])
    S[a], S[b] = domain.of(Interval)
    assert domain.is_closed
    assert _f == f._subs(z, xi)
    return Any[xi:domain](All[z:domain](f <= _f))


@prove
def prove(Eq):
    from Lemma import Calculus

    a, b = Symbol(real=True)
    f = Function(real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(a < b, is_continuous(f, a, b))

    @Function
    def g(x):
        return -f(x)
    x = Eq[1].find(Limit).variable
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    ξ = Eq[1].variable
    Eq << Eq[1].subs(Eq[-1], Eq[-1].subs(x, ξ))

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Mul)

    Eq << Calculus.Any.All.Ge.of.Lt.IsContinuous.extreme_value_theorem.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].subs(Eq.g_def, Eq.g_def.subs(x, ξ))

    Eq << -Eq[-1].this.expr.expr
    # https://en.wikipedia.org/wiki/Extreme_value_theorem



if __name__ == '__main__':
    run()
# created on 2023-10-15
