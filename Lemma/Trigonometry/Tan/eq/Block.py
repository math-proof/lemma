from util import *


@apply
def apply(self):
    from Lemma.Trigonometry.Sin.eq.Block import rewrite
    return Equal(self, rewrite(Tan, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    Eq << apply(Tan(BlockMatrix([[A, B], [C, D]])))

    i = Symbol(domain=Range(n * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)

    j = Symbol(domain=Range(n * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Tan.eq.Ite)

    Eq << Eq[-1].this.find(Tan[Piecewise]).apply(Trigonometry.Tan.eq.Ite)

    Eq << Eq[-1].this.find(Tan[Piecewise]).apply(Trigonometry.Tan.eq.Ite, simplify=0)




if __name__ == '__main__':
    run()
# created on 2023-06-08
