from util import *


@apply
def apply(given):
    from sympy.concrete.limits import limits_cond
    expr, *limits = given.of(All)

    assert len(limits) > 1

    limit, *limits = limits
    cond = limits_cond((limit,))
    return All(expr | cond.invert(), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    A, B = Symbol(etype=dtype.real)
    x, y = Symbol(real=True)
    f = Function(real=True)

    Eq << apply(All[x:A, y:B](f(x, y) > 0))

    Eq << Eq[1].this.expr.apply(Bool.All.of.All_OrNot, pivot=1)


if __name__ == '__main__':
    run()

# created on 2018-12-12
