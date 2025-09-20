from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Imply[Greater, Equal[Indexed, 0]])
    n = L.shape[1]
    return Equal(L[i, i + 1:], Zeros(n - i - 1))

@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Tensor

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Imply(j > i, Equal(L[i, j], 0)))

    Eq << Logic.All.of.Imp.apply(Eq[0], j)

    Eq << Algebra.All.of.All.limits.domain_defined.apply(Eq[-1], j)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
