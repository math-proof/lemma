from util import *


@apply
def apply(self, doit=True, deep=True):
    args = self.of(Det[MatMul])
    args = [Det(arg) for arg in args]
    if doit:
        args = [arg.doit(deep=deep) for arg in args]

    return Equal(self, Mul(*args))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    A, B, C = Symbol(shape=(n, n), complex=True)
    Eq << apply(Det(A @ B @ C))

    D = Symbol(A @ B)
    Eq << Eq[0].subs(D.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul.deux)

    Eq << Eq[-1].this.lhs.args[1].arg.definition

    Eq << Eq[-1].this.find(Det[MatMul]).apply(Discrete.Det.eq.Mul.deux)





if __name__ == '__main__':
    run()
# created on 2020-08-20
# updated on 2023-03-21
from . import deux
