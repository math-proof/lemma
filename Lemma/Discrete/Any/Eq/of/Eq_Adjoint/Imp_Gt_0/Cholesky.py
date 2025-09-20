from util import *


@apply
def apply(eq, infer, L):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    assert L.is_complex
    return Exists[L](Equal(A, L @ ~L.T))

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Logic

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), complex=True)
    Eq << apply(Equal(~A.T, A),
               Imply(Unequal(x, Zeros(n)), ~x @ A @ x > 0), L)

    i, j = Symbol(integer=True)
    Eq << Discrete.Any.And.of.Eq_Adjoint.Imp_Gt_0.Cholesky.apply(*Eq[:2], L, i, j)

    Eq << Logic.Any.of.Any_And.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-07-02
