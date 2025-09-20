from util import *


@apply
def apply(self):
    expr, (x, cond, space) = self.of(Sum)
    cond &= Element(x, space)
    return Equal(self, Sum[x:cond](expr))


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer[n])

    x = Symbol(integer=True, shape=(oo,))
    f, g = Function(real=True, shape=())
    Eq << apply(Sum[x[:n]:g(x[:n]) > 0:A](f(x[:n])))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

if __name__ == '__main__':
    run()

# created on 2020-03-14
