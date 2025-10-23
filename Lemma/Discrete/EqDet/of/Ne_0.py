from util import *


@apply
def apply(given):
    A_det, S[0] = given.of(Unequal)
    A = A_det.of(Determinant)
    return Equal(Cofactors(A).T / Determinant(A), Inverse(A))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Nat

    n = Symbol(integer=True, positive=True)
    A = Symbol(complex=True, shape=(n, n))
    Eq << apply(Unequal(Determinant(A), 0))

    Eq << Tensor.Dot.eq.Mul.adjugate.apply(A)

    Eq << Nat.Eq_Div.of.Eq.Ne_0.apply(Eq[0], Eq[-1])

    Eq << Discrete.EqInv.of.Eq.apply(Eq[-1])

    Eq << Nat.Eq_Div.of.Eq.Ne_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].lhs.args[0].base @ Eq[-1]

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
# created on 2020-02-12
# updated on 2023-05-21
