from util import *


@apply
def apply(eq, i, j):
    A, S[~A.T] = eq.of(Equal)
    n = A.shape[-1]
    return Equal(ReducedSum(ReducedSum(A)), Sum[i:n](A[i, i]) + 2 * Sum[j:i, i:n](Re(A[i, j])))

@prove
def prove(Eq):
    from Lemma import Algebra, Vector

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A, ~A.T), i, j)

    Eq << Eq[1].lhs.this.apply(Vector.Sum.eq.Sum_Get, i)

    Eq << Eq[-1].this.rhs.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split.limits)

    Eq << Eq[0][j, i]

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Add[Conjugate]).apply(Algebra.Add.eq.Mul.Re)




if __name__ == '__main__':
    run()
# created on 2023-05-25
