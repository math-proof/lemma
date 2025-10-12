from util import *


@apply
def apply(is_positive, eq, x=None):
    fx, (x_, d) = is_positive.of(Derivative < 0)
    assert d == 2

    wi, (i, n) = eq.of(Equal[Sum[Tuple[0, Expr]], 1])
    assert wi >= 0

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol(shape=(oo,), domain=domain)
    assert x.domain_assumed == domain
    return LessEqual(Sum[i:n](wi * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](wi * x[i])))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Finset

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol(shape=(oo,), nonnegative=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) < 0, Equal(Sum[i:n](w[i]), 1))

    Eq << -Eq[0]

    Eq << Eq[-1].this.lhs.apply(Calculus.Mul.eq.Grad)

    Eq << Calculus.Ge.of.Gt_0.Eq.Jesson.apply(Eq[-1], Eq[1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.apply(Finset.Mul_Sum.eq.Sum_Mul)


if __name__ == '__main__':
    run()
# created on 2020-06-27
