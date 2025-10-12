from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Imply[Greater, Equal[Indexed, 0]])
    return Equal(L[i, Min(i, j) + 1:] @ ~L[j, Min(i, j) + 1:], 0)

@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Imply(j > i, Equal(L[i, j], 0)))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=j > i)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.EqMin.of.Gt, ret=0), Eq[-1].this.lhs.apply(Nat.EqMin.of.Le, ret=0)

    Eq <<= Bool.Imp_And.given.Imp.And.subst.apply(Eq[-2]), Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1])

    Eq <<= Bool.Imp_And.given.Imp.delete.apply(Eq[-2], 0), Bool.Imp_And.given.Imp.delete.apply(Eq[-1], 0)

    Eq <<= Bool.Imp.given.All.apply(Eq[-2], i), Bool.Imp.given.All.apply(Eq[-1], j)

    Eq << Bool.Eq_0.Slice.of.Imp_Eq_0.apply(Eq[0])

    Eq << Eq[-1].subs(i, j)

    Eq <<= Eq[-4].subs(Eq[-2]), Eq[-3].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
