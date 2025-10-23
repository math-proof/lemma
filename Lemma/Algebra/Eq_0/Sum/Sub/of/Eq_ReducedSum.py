from util import *


@apply
def apply(eq_x_bar, k=None):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k')
    return Equal(Sum[k:n](x[k] - x_bar[n]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset, Finset

    x = Symbol(real=True, shape=(oo,))
    σ2 = Symbol("σ^2", shape=(oo,))
    s2 = Symbol("s^2", shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), k)

    Eq << Eq[1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[0] * n

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)


if __name__ == '__main__':
    run()
# created on 2023-11-06
