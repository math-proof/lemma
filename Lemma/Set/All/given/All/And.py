from util import *


@apply
def apply(given):
    function, (x, domain) = given.of(All)

    assert domain.is_set

    return All[x:domain](function & Unequal(domain, x.emptySet))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    A = Symbol(etype=dtype.real, given=True)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(All[e:A](f(e) > 0))

    Eq << Logic.All.All.of.All_And.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-01-08
