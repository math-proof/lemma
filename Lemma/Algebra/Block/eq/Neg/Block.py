from util import *


@apply
def apply(self, *, simplify=True):
    assert self.is_BlockMatrix
    args = [-arg for arg in self.args]
    return Equal(self, -BlockMatrix[self.axis](args).simplify(), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(BlockMatrix(-A, -B))

    i = Symbol(domain=Range(m * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)




if __name__ == '__main__':
    run()
# created on 2023-09-18
