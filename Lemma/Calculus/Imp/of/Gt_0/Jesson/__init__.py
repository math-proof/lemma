from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol(shape=(oo,), nonnegative=True)
    else:
        assert w >= 0

    if i is None:
        i = Symbol(integer=True)

    if n is None:
        n = Symbol(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Imply(Equal(Sum[i:n](w[i]), 1), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from Lemma import Calculus

    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol(shape=(oo,), nonnegative=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq << Calculus.Imp.of.Gt_0.Jesson.induct.apply(Eq[0], w=w, n=n)


if __name__ == '__main__':
    run()
# created on 2020-06-01

from . import induct
