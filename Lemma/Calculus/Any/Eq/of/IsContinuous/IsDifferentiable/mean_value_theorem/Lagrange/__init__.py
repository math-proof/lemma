from util import *


@apply
def apply(is_continuous, is_differentiable):
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_differentiable, of_continuous
    fz, (z, a, b) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)
    assert a < b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b, left_open=True, right_open=True)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from Lemma import Calculus

    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    a = Symbol(real=True)
    b = Symbol(domain=Interval.open(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b))

    Eq << Less(a, b, plausible=True)

    Eq << Calculus.Any.Eq.of.Lt.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange.apply(Eq[-1], Eq[0], Eq[1])






































if __name__ == '__main__':
    run()


# created on 2020-06-17
from . import close
