from util import *


@apply
def apply(self):
    args = self.of(Determinant[Mul])
    for i, vector in enumerate(args):
        if len(vector.shape) == 1:
            break
    args = args[:i] + args[i + 1:]
    n, = vector.shape
    i = self.generate_var(integer=True, var='i')
    return Equal(self, Product[i:n](vector[i]) * Det(Mul(*args)))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    X = Symbol(shape=(n, n), complex=True)
    a = Function(real=True)
    i = Symbol(integer=True)
    Eq << apply(Determinant(Stack[i:n](a(i)) * X))




if __name__ == '__main__':
    run()
# created on 2022-01-15

