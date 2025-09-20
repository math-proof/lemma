from util import *


@apply
def apply(n):
    k = Symbol(integer=True)

    return Equal(Stack[k:n + 1](KroneckerDelta(k, n)), BlockMatrix(Zeros(n), 1))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    Eq << apply(n)

    U = Symbol(Eq[0].lhs)
    V = Symbol(Eq[0].rhs)
    Eq << U.this.definition

    Eq << V.this.definition

    i = Symbol(domain=Range(n + 1))
    Eq << Eq[-1][i]

    Eq << U[i].this.definition

    Eq << Eq[-2].this.rhs.apply(Algebra.Ite.eq.AddMulS)

    Eq << Eq[-2] - Eq[-1]

    Eq << Algebra.Eq.of.Sub.eq.Zero.apply(Eq[-1])

    Eq << Eq[-1].apply(Tensor.EqStackS.of.Eq, (i,))

    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2])




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-09
# updated on 2022-01-01
