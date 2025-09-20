from util import *


@apply
def apply(self, index=0):
    from Lemma.Algebra.Sum.limits.pop.Slice import rewrite
    return Equal(self, rewrite(Cup, self, index))


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(etype=dtype.integer, shape=())
    Eq << apply(Cup[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.simplify()




if __name__ == '__main__':
    run()
# created on 2023-07-02
# updated on 2023-11-18
