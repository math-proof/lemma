from util import *


@apply
def apply(self):
    base, e = self.of(Determinant[MatPow])
    return Equal(self, Det(base) ** e)


@prove(proved=False)
def prove(Eq):
    n, k = Symbol(integer=True, positive=True)
    A = Symbol(complex=True, shape=(n, n))
    Eq << apply(Determinant(A ^ -k))


if __name__ == '__main__':
    run()
# created on 2023-05-01
