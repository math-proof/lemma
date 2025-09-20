from util import *


@apply
def apply(self):
    (f, (i, a, b)), S[f._subs(i, b)] = self.of(MatMul[MatProduct])
#     b >= a => b + 1 >= a
    return Equal(self, MatProduct[i:a:b + 1](f))


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProduct[i:n](f(i)) @ f(n))





if __name__ == '__main__':
    run()
# created on 2021-12-13
