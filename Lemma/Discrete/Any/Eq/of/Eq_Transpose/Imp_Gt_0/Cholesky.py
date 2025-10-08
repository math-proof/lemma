from util import *


@apply
def apply(eq, infer, L):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    assert L.is_real
    return Exists[L](Equal(A, L @ L.T))

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), real=True)
    Eq << apply(Equal(A.T, A),
               Imply(Unequal(x, Zeros(n)), x @ A @ x > 0), L)

    i, j = Symbol(integer=True)
    Eq << Discrete.Any.And.of.Eq_Transpose.Imp_Gt_0.Cholesky.apply(*Eq[:2], L, i, j)

    Eq << Bool.Any.of.Any_And.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-07-02
