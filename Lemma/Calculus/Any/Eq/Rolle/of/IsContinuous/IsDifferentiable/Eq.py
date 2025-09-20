from util import *


@apply
def apply(is_continuous, is_differentiable, equal):
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import of_continuous, of_differentiable
    fz, (z, a, b) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)

    assert a < b
    S[fz._subs(z, a)], S[fz._subs(z, b)] = equal.of(Equal)

    return Any[z:a:b](Equal(Derivative(fz, z), 0))


@prove
def prove(Eq):
    from Lemma import Calculus

    from Lemma.Calculus.All.Any.Eq.of.All_Eq.intermediate_value_theorem import is_continuous
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    a = Symbol(real=True)
    b = Symbol(domain=Interval.open(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))

    Eq << Less(a, b, plausible=True)

    Eq << Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq.apply(Eq[-1], Eq[0], Eq[1], Eq[2])

    # https://math.stackexchange.com/questions/261903/rolle-and-mean-value-theorem?rq=1

if __name__ == '__main__':
    run()

# created on 2020-06-16
