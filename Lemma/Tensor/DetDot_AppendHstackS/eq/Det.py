from util import *


@apply
def apply(self):
    A, B = self.of(Det[Expr @ BlockMatrix[BlockMatrix[1][Identity, Expr], BlockMatrix[1][Zeros, Identity]]])

    return Equal(self, Det(A))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(2 * n, 2 * n), complex=True)
    B = Symbol(shape=(n, n), complex=True)
    Eq << apply(Det(A @ BlockMatrix([[Identity(n), B], [Zeros(n, n), Identity(n)]])))

    
    


if __name__ == '__main__':
    run()
# created on 2020-08-18
# updated on 2021-12-13