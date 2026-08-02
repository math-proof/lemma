from util import *


@apply
def apply(eq):
    (w, i, j), (S[i], S[j]) = eq.of(Equal[Indexed, SwapMatrix])
    n = w.shape[-1]
    return Equal(w[i, j] @ w[i, j], Identity(n))


@prove
def prove(Eq):
    n = Symbol(positive=True, integer=True)
    i, j = Symbol(integer=True)
    w = Symbol(real=True, shape=(n, n, n, n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    Eq << Eq[0] @ Eq[0]

    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-24
# updated on 2023-05-21
