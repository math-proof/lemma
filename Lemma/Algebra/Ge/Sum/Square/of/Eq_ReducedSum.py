from util import *


@apply
def apply(eq_x_bar, t, k=None):
    ((x, (S[0], n)), S[n]), x_bar = eq_x_bar.of(Equal[ReducedSum[Sliced] / Symbol])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k', excludes=t.free_symbols)
    return Sum[k:n]((x[k] - t) ** 2) >= Sum[k:n]((x[k] - x_bar) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Rat

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    t = Symbol(real=True)
    x_bar = Symbol(r"{\bar {x}}", real=True)
    Eq << apply(Equal(x_bar, ReducedSum(x[:n]) / n), t, k)

    Eq << Algebra.Eq.Sum.Square.eq.Add.Sum.Square.of.Eq_ReducedSum.apply(Eq[0], t, k)

    Eq << GreaterEqual(Eq[-1].rhs.find(Add ** 2), 0, plausible=True)

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Bool.Cond.of.And.apply(Eq[-1], 1).reversed

    Eq << Algebra.GeMul.of.Gt_0.Ge.apply(Eq[-1], Eq[-3])

    Eq << Algebra.GeAdd.of.Ge.Eq.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-11-06
