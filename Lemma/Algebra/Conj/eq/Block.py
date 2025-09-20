from util import *


@apply
def apply(self):
    from Lemma.Trigonometry.Sin.eq.Block import rewrite
    return Equal(self, rewrite(Conjugate, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(complex=True, shape=(n, n))
    Eq << apply(Conjugate(BlockMatrix([[A, B], [C, D]]), evaluate=False))

    i = Symbol(domain=Range(n * 2))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], i)






if __name__ == '__main__':
    run()
# created on 2023-09-18
