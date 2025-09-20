from util import *


@apply
def apply(sgm, *, simplify=False):
    expr, *limits = sgm.of(Sum)
    limit, *limits = limits
    assert limits
    expr = Sum(expr, limit).simplify()
    rhs = Sum(expr, *limits, evaluate=simplify)
    return Equal(sgm, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:n, j:n](f[j] * g[i, j]))

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul_Sum.eq.Sum_Mul)





if __name__ == '__main__':
    run()

# created on 2019-11-11
# updated on 2023-06-02
from . import Ite
