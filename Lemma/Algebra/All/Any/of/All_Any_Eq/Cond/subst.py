from util import *


@apply
def apply(all_any, cond, reverse=False):
    assert not cond.is_Quantifier
    (fn, *limits_e), *limits_f = all_any.of(All[Any])

    x, y = fn.of(Equal)
    if reverse:
        x, y = y, x

    return All(Any(cond._subs(x, y), *limits_e), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    A, B = Symbol(etype=dtype.integer)

    Eq << apply(All[y:B](Any[x:A](Equal(g(x, y), f(x, y)))), g(x, y) > y)

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[1], Eq[0])

    Eq << Eq[-1].this.expr.apply(Algebra.Any.of.Any_Eq.Cond.subst)


if __name__ == '__main__':
    run()

# created on 2018-12-25
