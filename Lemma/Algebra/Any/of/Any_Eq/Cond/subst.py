from util import *


@apply
def apply(any_eq, cond, reverse=False):
    assert not cond.is_Quantifier
    (x, y), *limits = any_eq.of(Any[Equal])

    if reverse:
        x, y = y, x
    return Any(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    S = Symbol(etype=dtype.integer)

    Eq << apply(Any[x:S](Equal(g(x), f(x))), g(x) > y)

    Eq << Logic.Any_And.of.Any.All.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst)


if __name__ == '__main__':
    run()

# created on 2018-12-24
