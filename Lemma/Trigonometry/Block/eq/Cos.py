from util import *


@apply
def apply(self):
    from Lemma.Algebra.Block.eq.Exp import extract
    return Equal(self, Cos(extract(Cos, self)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    n = Symbol(positive=True, integer=True)
    A, B, C, D = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix([[Cos(A), Cos(B)], [Cos(C), Cos(D)]]))

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Cos.eq.Block)


if __name__ == '__main__':
    run()
# created on 2023-06-08
