from util import *


@apply
def apply(given, epsilon=None):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    a, b = domain.of(Interval)
    assert domain.is_closed

    if not isinstance(epsilon, Basic):
        if epsilon is None:
            epsilon = 'epsilon'
        epsilon = given.generate_var(real=True, var=epsilon)

    return Any[epsilon:0:1](Equal(Integral(f, (z, a, b)), (b - a) * f._subs(z, a * epsilon + b * (1 - epsilon))))


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus

    a, b = Symbol(real=True)
    f = Function(real=True)
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()
# created on 2020-05-02
