from util import *


@apply
def apply(given, index=None):
    function, *limits = given.of(Any)
    if index is None:
        cond = given.limits_cond
    else:
        from Lemma.Logic.Any_And.of.AnySetOf_AnySetOf import limits_cond
        x, cond = limits_cond(limits, index)

    return Any((function & cond).simplify(), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    f, g, h = Function(shape=(), integer=True)
    Eq << apply(Any[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))

    Eq << Logic.Any_And.of.AnySetOf_AnySetOf.apply(Eq[0])

    Eq << Logic.AnySetOf.given.Any_And.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-02-19
