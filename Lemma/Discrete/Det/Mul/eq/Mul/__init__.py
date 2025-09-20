from util import *


@apply
def apply(self):
    matrix, scalar = std.array_split(self.of(Det[Mul]), lambda arg: arg.shape)
    scalar = Mul(*scalar)
    matrix = Mul(*matrix)

    n = matrix.shape[-1]
    return Equal(self, scalar ** n * Det(matrix))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    X = Symbol(shape=(n, n), complex=True)
    a = Symbol(complex=True)
    Eq << apply(Det(a * X))

    i = Symbol(integer=True)
    @Function(complex=True)
    def f(i):
        return a

    Eq << (X * Stack[i:n](f(i))).this.find(f).defun()

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.Mul.eq.Mul.Prod)

    Eq << Eq[-1].this.find(f).defun()



if __name__ == '__main__':
    run()
# created on 2020-08-19
# updated on 2022-01-15
from . import Prod
