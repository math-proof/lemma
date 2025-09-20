from util import *


@apply
def apply(self):
    blocks = self.blocks
    for i in range(len(blocks)):
        for j in range(len(blocks[i])):
            if j == i:
                assert blocks[i][j].is_Identity or blocks[i][j].is_One
            else:
                assert blocks[i][j].is_zero
    return Equal(self, Identity(self.shape[-1]))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Tensor

    n, m = Symbol(integer=True, positive=True)
    Eq << apply(BlockMatrix([[Identity(n), Zeros(n, m)], [Zeros(m, n), Identity(m)]]))

    i = Symbol(domain=Range(n + m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    j = Symbol(domain=Range(n + m))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Logic.Cond_Ite.given.And.Imp.apply(Eq[-1])

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Lt.of.Lt.Ge), Eq[-1].this.lhs.apply(Algebra.Gt.of.Lt.Ge)

    Eq << Eq[-2].this.lhs.apply(Algebra.Ne.of.Lt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.of.Gt)





if __name__ == '__main__':
    run()
# created on 2023-06-16
# updated on 2023-08-19
