from util import *


@apply
def apply(all_is_positive):
    (fx, (x, S[2])), (S[x], a, b) = all_is_positive.of(All[Derivative > 0])
    from Lemma.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    f = lambda t: fx._subs(x, t)
    return is_differentiable(f, a, b)


@prove(proved=False)
def prove(Eq):
    a, b, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](Derivative(f(x), (x, 2)) > 0))


if __name__ == '__main__':
    run()
# created on 2020-03-30

from . import In
