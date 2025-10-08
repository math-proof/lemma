from util import *


@apply
def apply(infer, j=None):
    x, (S[~x], A, S[x]) = infer.of(Imply[Unequal[0], MatMul > 0])
    if j is None:
        j = infer.generate_var(integer=True)
    return A[j, j] > 0

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor, Bool

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    i = Symbol(integer=True)
    Eq << apply(Imply(Unequal(x, Zeros(n)), (~x) @ A @ x > 0), i)

    j = Symbol(domain=Range(n))
    Eq << Eq[0].subs(x, Stack[i:n](KroneckerDelta(i, j)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.given.Any.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.given.Cond.subst, i, j)

    Eq << Eq[-1].this.lhs.args[:2].apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Sum)

    Eq << Bool.All.of.Cond.apply(Eq[-1], j)

    j = Eq[-1].lhs.index
    Eq << Eq[-1].subs(j, i)




if __name__ == '__main__':
    run()
# created on 2023-05-01
