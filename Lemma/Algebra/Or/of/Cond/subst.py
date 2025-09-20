from util import *


@apply
def apply(given, old, new):
    from Lemma.Logic.Or_Not.of.All import rewrite_as_Or
    assert new not in old.domain
    domain = old.domain_bounded
    assert domain is not None and new not in domain
    assert given._has(old)

    from Lemma.Logic.All.of.Cond import all
    cond = all(given, old)
    old = old.unbounded
    assert old != new
    ou = rewrite_as_Or(cond)

    return ou._subs(old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x, j = Symbol(integer=True)
    y = Symbol(integer=True, shape=(oo,))
    t = Symbol(domain=Range(n + 1))
    f, g = Function(integer=True)
    Eq << apply(f(x, t) > g(t), t, y[j])

    Eq << Logic.All.of.Cond.apply(Eq[0], t)

    t = Eq[-1].variable
    Eq << Logic.Or_NotIn.of.All.apply(Eq[-1], t, y[j])


if __name__ == '__main__':
    run()

# created on 2019-03-19
