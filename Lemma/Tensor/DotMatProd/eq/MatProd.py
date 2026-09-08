from util import *


@apply
def apply(self):
    (f, (i, a, b)), S[f._subs(i, b)] = self.of(MatMul[MatProd])
#     b >= a => b + 1 >= a
    return Equal(self, MatProd[i:a:b + 1](f))


@prove
def prove(Eq):
    from Lemma import Tensor

    i = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProd[i:n](f(i)) @ f(n))

    Eq << Tensor.MatProd.eq.DotMatProd.apply(Eq[0].rhs).reversed


if __name__ == '__main__':
    run()
# created on 2021-12-13
