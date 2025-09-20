from util import *


@apply
def apply(self):
    front, (f, (i, a, b)) = self.of(MatMul[MatProduct])
    assert front == f._subs(i, a - 1)
#     b >= a => b + 1 >= a
    return Equal(self, MatProduct[i:a - 1:b](f))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(f(0) @ MatProduct[i:1:n](f(i)))


if __name__ == '__main__':
    run()
# created on 2021-12-13
