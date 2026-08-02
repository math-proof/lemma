from util import *


@apply
def apply(self):
    args = self.of(Determinant[Mul])
    scalar = []
    for arg in args:
        if arg.shape:
            n = arg.shape[-1]
            assert arg.is_Identity
        else:
            scalar.append(arg)
    scalar = Mul(*scalar)

    return Equal(self, scalar ** n)


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    a = Symbol(complex=True)
    Eq << apply(Determinant(a * Identity(n)))


if __name__ == '__main__':
    run()
# created on 2021-08-31
