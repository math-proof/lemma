from util import *


@apply
def apply(self):
    (base, S[-1]), B = self.of(MatPow @ Expr)
    A = base - B
    return Equal(self, Identity(B.shape[0]) - (base ^ -1) @ A, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n, n), complex=True)
    Eq << apply(((A + B) ^ -1) @ B)

    Eq << Algebra.Eq.given.Eq.transport.apply(Eq[0], rhs=0)

    Eq << Eq[-1].this.lhs.apply(Tensor.Add.eq.Dot)


if __name__ == '__main__':
    run()
# created on 2023-04-30
from . import push
