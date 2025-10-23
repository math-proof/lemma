from util import *


@apply
def apply(imply, simplify=True):
    from sympy.concrete.expr_with_limits import ExprWithLimits
    All_Eq, cond = imply.of(And)
    if not All_Eq.is_ForAll:
        All_Eq, cond = cond, All_Eq
    (old, new), *limits = All_Eq.of(All[Equal])
    limits = tuple(limits)

    for expr in cond.finditer(ExprWithLimits):
        if expr.expr._has(old) and expr.limits == limits:
            break
    else:
        return

    function = expr.expr._subs(old, new)
    if simplify:
        function = function.simplify()

    expr_ = expr.func(function, *limits)
    if simplify:
        expr_ = expr_.simplify()

    cond = cond._subs(expr, expr_)

    return All_Eq, cond


@prove
def prove(Eq):
    from Lemma import Algebra, Finset
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    a, b = Symbol(integer=True, shape=(oo,))

    S = Symbol(etype=dtype.integer)

    Eq << apply(All[i:n](Equal(a[i], b[i])) & Element(Sum[i:n](a[i]), S))

    Eq << Finset.EqSumS.of.All_Eq.apply(Eq[-2])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-05-02
