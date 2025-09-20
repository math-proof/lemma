from util import *


@apply
def apply(self):
    from Lemma.Algebra.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Product[i:k, k:n](f(k, i)) * Product[j:k, k:n](g(k, j)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod_Mul.eq.MulProdS)




if __name__ == '__main__':
    run()

# created on 2018-04-14
# updated on 2023-08-20
