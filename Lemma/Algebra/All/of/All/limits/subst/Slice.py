from util import *


@apply
def apply(given, old, new):
    function, (var, domain) = given.of(All)

    assert old.is_Sliced and old == var
    assert new.is_Sliced and new.base.is_symbol and new.base.is_given is None

    return All[new:domain](function._subs(old, new))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, positive=True)

    a, b = Symbol(real=True)
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True, shape=())

    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n)](f(x[:n]) > 0), x[:n], x[1:n + 1])

    Eq << Bool.Or_NotIn.of.All.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << Bool.All.given.All_Or_Not.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-12-16
