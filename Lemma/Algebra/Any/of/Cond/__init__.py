from util import *


@apply
def apply(cond, wrt=None):
    assert cond._has(wrt)
    return Any[wrt](cond)


@prove
def prove(Eq):
    from Lemma import Set
    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, wrt=e)

    S = Symbol(Integers)
    Eq << All[e:S](f(e) > 0, plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Unequal(S, S.etype.emptySet, plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Set.Any.of.All.Ne_Empty.apply(Eq[-1], Eq[2])

    Eq << Eq[-1].this.limits[0][1].definition


if __name__ == '__main__':
    run()

# created on 2018-12-01
from . import subst
