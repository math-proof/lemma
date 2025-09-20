from util import *


@apply
def apply(self):
    expr, limit, *limits = self.of(Sum)

    assert limit[0].is_integer

    expr = Stack(expr, limit).simplify()
    if self.shape:
        expr = expr.T

    rhs = ReducedSum(expr)
    if limits:
        rhs = Sum(rhs, *limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y = Symbol(shape=(n, n), real=True)
    Eq << apply(Sum[i:n, j:n](y[j, i]))
    Eq << Eq[-1].this.rhs.expr.apply(Algebra.ReducedSum.eq.Sum)


if __name__ == '__main__':
    run()
# created on 2020-03-26
