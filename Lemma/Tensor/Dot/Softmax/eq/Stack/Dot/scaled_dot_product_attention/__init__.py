from util import *


@apply
def apply(self, i):
    ((Q, KT), d_sqrt), V = self.of(Softmax[Expr @ Expr / Expr] @ Expr)
    n = V.shape[0]
    return Equal(self, Stack[i:n](softmax(Q[i] @ KT / d_sqrt) @ V))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z)) @ V, i)

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-08-07
# updated on 2023-05-22


from . import double_limits
