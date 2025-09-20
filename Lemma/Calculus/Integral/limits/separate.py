from util import *


@apply
def apply(sgm, *, simplify=True):
    expr, *limits = sgm.of(Integral)
    assert len(limits) > 1
    limit, *limits = limits

    expr = sgm.func(expr, limit)
    if simplify:
        expr = expr.simplify()

    rhs = sgm.func(expr, *limits, evaluate=simplify)
    return Equal(sgm, rhs)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, y, a, b, c, d = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b, y:c:d](f(y) * g(x, y)))

    Eq << Eq[-1].this.rhs.expr.apply(Calculus.Mul.eq.Integral)


if __name__ == '__main__':
    run()
# created on 2020-06-06
