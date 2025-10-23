from util import *


@apply
def apply(eq_x_bar):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    return Equal(n * (x_bar[n] - x_bar[n + 1]) ** 2 + (x[n] - x_bar[n + 1]) ** 2, (x[n] - x_bar[n]) * (x[n] - x_bar[n + 1]))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Bool, Nat, Nat, Nat, Int

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n))

    Eq << Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, lhs=1)

    Eq << Eq[-1].this.rhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Square.Neg)

    Eq << Algebra.Eq.given.Eq.Div.apply(Eq[-1], Eq[-1].find((~Add) ** 2))

    Eq << Discrete.EqDiff.of.Eq_ReducedSum.apply(Eq[0])

    Eq.diff = Eq[-1].this.lhs.doit()

    Eq << Algebra.Sub.eq.Mul.of.Eq_ReducedSum.apply(Eq[0])

    Eq << Eq.diff * n

    Eq << Bool.Eq.of.Eq.Eq.apply(*Eq[-2:]).reversed




if __name__ == '__main__':
    run()
# created on 2023-11-06
